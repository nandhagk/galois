(** * Occurrence-pivot layouts

    Source positions distinguish repeated positive atoms and determine the tagged rule layout.
    For example, two identical body atoms have different positions and different frontier variants.
    Builds on: DatalogSemiNaive and the public source firing interface. *)

From Stdlib Require Import List Bool PeanoNat Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Datalog Require Import DatalogSyntax DatalogStratify DatalogFire DatalogSemiNaive.
Import List.ListNotations SemiNaive.
Local Open Scope nat_scope.

Module SemiNaiveSyntax.

(** The proof inventory numbers positive occurrences and leaves negative literals unnumbered. *)
Fixpoint occurrences {P} position (ls : list (literal P)) : list (nat * atom P) :=
  match ls with
  | [] => []
  | LPos a :: rest => (position, a) :: occurrences (S position) rest
  | LNeg _ :: rest => occurrences position rest
  end.

Lemma occurrence_level {P} position (ls : list (literal P)) i a :
  In (i, a) (occurrences position ls) -> position <= i.
Proof.
  revert position; induction ls as [|[x | x] ls IH]; intros position Hin; cbn in Hin;
    [contradiction | |].
  - destruct Hin as [Heq | Hin]; [injection Heq as <-; lia |].
    pose proof (IH (S position) Hin); lia.
  - apply (IH position Hin).
Qed.

Lemma occurrence_unique {P} position (ls : list (literal P)) i a b :
  In (i, a) (occurrences position ls) ->
  In (i, b) (occurrences position ls) -> a = b.
Proof.
  revert position; induction ls as [|[x | x] ls IH]; intros position Ha Hb; cbn in Ha, Hb;
    [contradiction | |].
  - destruct Ha as [Ha | Ha], Hb as [Hb | Hb].
    + congruence.
    + injection Ha as <- <-; pose proof (occurrence_level _ _ _ _ Hb); lia.
    + injection Hb as <- <-; pose proof (occurrence_level _ _ _ _ Ha); lia.
    + apply (IH (S position)); assumption.
  - apply (IH position); assumption.
Qed.

(** Each source positive atom has an occurrence and each occurrence names a source positive atom. *)
Theorem occurrences_spec {P} position (ls : list (literal P)) a :
  (exists i, In (i, a) (occurrences position ls)) <-> In (LPos a) ls.
Proof.
  revert position; induction ls as [|[x | x] ls IH]; intro position; cbn.
  - split; [intros [i Hbad]; contradiction | contradiction].
  - split.
    + intros [i [Heq | Hin]]; [left; congruence | right; apply (IH (S position)); eauto].
    + intros [Heq | Hin].
      * injection Heq as <-; exists position; now left.
      * destruct (proj2 (IH (S position)) Hin) as [i Hi]; exists i; now right.
  - rewrite <- (IH position); split.
    + intros [i Hi]; right; exists i; exact Hi.
    + intros [Hbad | Hin]; [discriminate | exact Hin].
Qed.

Lemma pivots_from_equation {P} (st : stratification P) k position ls :
  Cost.value (pivots_from_c st k position ls) =
  match ls with
  | [] => []
  | LNeg _ :: rest => Cost.value (pivots_from_c st k position rest)
  | LPos a :: rest =>
    if Nat.eqb (level st (pred a)) k
    then position :: Cost.value (pivots_from_c st k (S position) rest)
    else Cost.value (pivots_from_c st k (S position) rest)
  end.
Proof.
  destruct ls as [|[a | a] ls]; reflexivity.
Qed.

(** Recursive pivot positions are precisely the same-level positive occurrences. *)
Theorem pivots_from_spec {P} (st : stratification P) k position ls i :
  In i (Cost.value (pivots_from_c st k position ls)) <->
  exists a, In (i, a) (occurrences position ls) /\ level st (pred a) = k.
Proof.
  revert position; induction ls as [|[x | x] ls IH]; intro position;
    rewrite pivots_from_equation; cbn [occurrences].
  - split; [contradiction | intros [a [Hbad _]]; contradiction].
  - destruct (Nat.eqb (level st (pred x)) k) eqn:Hlevel.
    + apply Nat.eqb_eq in Hlevel; cbn [In]; rewrite IH; split.
      * intros [<- | [a [Ha Hl]]].
        -- exists x; split; [left; reflexivity | exact Hlevel].
        -- exists a; split; [now right | exact Hl].
      * intros [a [[Heq | Ha] Hl]]; [left; congruence | right; exists a; auto].
    + rewrite IH; split.
      * intros [a [Ha Hl]]; exists a; split; [now right | exact Hl].
      * intros [a [[Heq | Ha] Hl]].
        -- injection Heq as <- <-; rewrite Hl, Nat.eqb_refl in Hlevel; discriminate.
        -- exists a; auto.
  - apply IH.
Qed.

Lemma classify_equation {P} (st : stratification P) k rs :
  classify st k rs =
  match rs with
  | [] => ([], [])
  | r :: rest =>
    let acc := classify st k rest in
    if Nat.eqb (level st (pred (head r))) k then
      match pivots st k r with
      | [] => (r :: fst acc, snd acc)
      | _ :: _ => (fst acc, map (fun i => (r, i)) (pivots st k r) ++ snd acc)
      end
    else acc
  end.
Proof.
  destruct rs as [|r rs]; [reflexivity |].
  unfold classify at 1; unfold classify_c; rewrite value_fold_right_c.
  cbn [fold_right].
  rewrite <- (value_fold_right_c (classify_one_c st k) ([], []) rs).
  fold (@classify P st k rs).
  unfold classify_one_c at 1; repeat rewrite Cost.value_bind.
  fold (level st (pred (head r))).
  destruct (Nat.eqb (level st (pred (head r))) k); [|reflexivity].
  rewrite Cost.value_bind; fold (pivots st k r).
  destruct (pivots st k r); [reflexivity |].
  repeat rewrite Cost.value_bind; rewrite value_app_c, value_map_c; reflexivity.
Qed.

(** Classification selects same-level source rules without recursive positive occurrences. *)
Theorem classify_seeds {P} (st : stratification P) k rs r :
  In r (fst (classify st k rs)) <->
    In r rs /\ level st (pred (head r)) = k /\ pivots st k r = [].
Proof.
  induction rs as [|x rs IH]; rewrite classify_equation.
  - cbn; tauto.
  - destruct (Nat.eqb (level st (pred (head x))) k) eqn:Hx.
    + apply Nat.eqb_eq in Hx; destruct (pivots st k x) as [|i positions] eqn:Hp;
        cbn [fst In]; rewrite IH; intuition congruence.
    + apply Nat.eqb_neq in Hx; cbn [In]; rewrite IH; intuition congruence.
Qed.

(** Classification retains every same-level rule and each of its recursive pivot positions. *)
Theorem classify_jobs {P} (st : stratification P) k rs r i :
  In (r, i) (snd (classify st k rs)) <->
    In r rs /\ level st (pred (head r)) = k /\ In i (pivots st k r).
Proof.
  induction rs as [|x rs IH]; rewrite classify_equation.
  - cbn; tauto.
  - destruct (Nat.eqb (level st (pred (head x))) k) eqn:Hx.
    + apply Nat.eqb_eq in Hx; destruct (pivots st k x) as [|j positions] eqn:Hp.
      * cbn [snd In]; rewrite IH; split.
        -- intros [Hr [Hl Hi]]; auto.
        -- intros [[<- | Hr] [Hl Hi]]; [rewrite Hp in Hi; contradiction | auto].
      * cbn [snd]; rewrite in_app_iff, in_map_iff, IH; cbn [In]; split.
        -- intros [[p [Heq Hin]] | [Hr [Hl Hi]]].
           ++ injection Heq as Heqr Heqi; subst r p.
              split; [now left | split; [exact Hx | rewrite Hp; exact Hin]].
           ++ auto.
        -- intros [[<- | Hr] [Hl Hi]].
           ++ left; exists i; split; [reflexivity | rewrite Hp in Hi; exact Hi].
           ++ right; auto.
    + apply Nat.eqb_neq in Hx; cbn [In]; rewrite IH; intuition congruence.
Qed.

Definition tagged_body {P} pivot position ls :=
  Cost.value (@tag_body_from_c P pivot position ls).

Lemma tagged_body_equation {P} pivot position (ls : list (literal P)) :
  tagged_body pivot position ls =
  match ls with
  | [] => []
  | LPos a :: rest =>
    LPos (Atom (pred a, Nat.eqb position pivot) (args a)) ::
      tagged_body pivot (S position) rest
  | LNeg a :: rest =>
    LNeg (Atom (pred a, false) (args a)) :: tagged_body pivot position rest
  end.
Proof.
  destruct ls as [|[a | a] ls]; reflexivity.
Qed.

Lemma tag_rule_equation {P} (r : rule P) pivot :
  tag_rule r pivot =
    Rule (Atom (pred (head r), false) (args (head r))) (tagged_body pivot 0 (body r)).
Proof.
  reflexivity.
Qed.

(** Tagged positives retain both the source atom and its unique positive occurrence position. *)
Theorem tagged_positive {P} pivot position ls (a : atom (P * bool)) :
  In (LPos a) (tagged_body pivot position ls) <->
  exists i source, In (i, source) (occurrences position ls) /\
    a = Atom (pred source, Nat.eqb i pivot) (args source).
Proof.
  revert position; induction ls as [|[x | x] ls IH]; intro position;
    rewrite tagged_body_equation; cbn [occurrences In].
  - split; [contradiction | intros [i [source [Hbad _]]]; contradiction].
  - rewrite IH; split.
    + intros [Heq | [i [source [Hin Heq]]]].
      * exists position, x; split; [now left | congruence].
      * exists i, source; split; [now right | exact Heq].
    + intros [i [source [[Heq | Hin] Ha]]].
      * injection Heq as <- <-; left; congruence.
      * right; exists i, source; auto.
  - rewrite IH; split.
    + intros [Hbad | Hin]; [discriminate | exact Hin].
    + intro Hin; now right.
Qed.

(** Tagged negatives always read the full side and have exactly the original negative arguments. *)
Theorem tagged_negative {P} pivot position ls (a : atom (P * bool)) :
  In (LNeg a) (tagged_body pivot position ls) <->
  exists source, In (LNeg source) ls /\ a = Atom (pred source, false) (args source).
Proof.
  revert position; induction ls as [|[x | x] ls IH]; intro position;
    rewrite tagged_body_equation; cbn [In].
  - split; [contradiction | intros [source [Hbad _]]; contradiction].
  - rewrite IH; split.
    + intros [Hbad | Hin]; [discriminate |].
      destruct Hin as [source [Hin Heq]]; exists source; auto.
    + intros [source [[Hbad | Hin] Heq]]; [discriminate |].
      right; exists source; auto.
  - rewrite IH; split.
    + intros [Heq | [source [Hin Ha]]].
      * exists x; split; [now left | congruence].
      * exists source; split; [now right | exact Ha].
    + intros [source [[Heq | Hin] Ha]].
      * injection Heq as <-; left; congruence.
      * right; exists source; auto.
Qed.

(** Positional tagging changes predicate selectors and preserves source range restriction. *)
Theorem tagged_safe {P} (r : rule P) pivot :
  safe_rule r -> safe_rule (tag_rule r pivot).
Proof.
  intros Hsafe v Hv; rewrite tag_rule_equation in *.
  cbn [head body] in Hv.
  assert (Horiginal : In v (atom_vars (head r)) \/
    exists a, In (LNeg a) (body r) /\ In v (atom_vars a)).
  { destruct Hv as [Hhead | [a [Hneg Hvar]]].
    - left; exact Hhead.
    - apply tagged_negative in Hneg as [source [Hsource ->]].
      right; exists source; split; [exact Hsource | exact Hvar]. }
  destruct (Hsafe v Horiginal) as [a [Ha Hvar]].
  destruct (proj2 (occurrences_spec 0 (body r) a) Ha) as [i Hi].
  exists (Atom (pred a, Nat.eqb i pivot) (args a)); split; [|exact Hvar].
  apply tagged_positive; exists i, a; auto.
Qed.

End SemiNaiveSyntax.
Import SemiNaiveSyntax.
