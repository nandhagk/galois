(** * Checked narrowing

    Each pass aggregates row contributions against a frozen store.
    For example, a rejected candidate leaves the input store unchanged.

    Main results
    - [narrow_candidate_spec] The candidate narrows joined contributions only when they lie below
      the old value.
    - [narrow_pass_spec] A pass accepts the candidate precisely when its check succeeds.
    - [refine_spec] Refinement performs the requested number of checked passes.
    - [narrow_pass_complexity] One pass is linear in the sweep measure of the program.
    - [refine_complexity] Refinement is linear in the pass count times the sweep measure.

    Builds on: Fixpoint.NarrowSig and Fixpoint.Query. *)

From Stdlib Require Import List Bool PeanoNat PArith NArith Lia.
From Argent Require Import Time Tactics Std Loop Complexity.
From Galois.Base Require Import Code MapSig Trie.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig CheckSig NarrowSig.
Import ComplexityNotations.
Import Code.List.

Module NarrowCode (L : WLATTICE_OPS) (S : SYSTEM_OPS L) (C : CHECK_OPS L S)
    <: NARROW_OPS L S C.
  Definition collect_one (sums : kmap S.key L.t) (xa : S.key * L.t) :=
    let '(x, a) := xa in
    let old := look_or S.key_code L.bot sums x in
    PTrieCode.set (S.key_code x) (x, L.join old a) sums.
  Definition collect_row p m sums r :=
    match eval_query (S.resume p) (C.look m) (Datatypes.S (length (S.deps p r)))
        (S.start p r) with
    | None => sums
    | Some (a, sides) => fold_left collect_one ((S.target p r, a) :: sides) sums
    end.
  Definition eval_all p m := fold_left (collect_row p m) (S.rows p) Empty.
  Definition narrow_one old sums acc (x : S.key) :=
    let code := S.key_code x in
    let aggregate := look_or S.key_code L.bot sums x in
    let before := C.look old x in
    let after := if L.leb aggregate before then L.narrow before aggregate else before in
    PTrieCode.set code (x, after) acc.
  Definition narrow_candidate p m :=
    let sums := eval_all p m in
    fold_left (narrow_one m sums)
      (flat_map (fun r => S.target p r :: S.sides p r) (S.rows p)) m.
  Definition narrow_pass p m :=
    let candidate := narrow_candidate p m in
    if C.check p candidate then candidate else m.
  Definition narrow_step p m : kmap S.key L.t + kmap S.key L.t :=
    let candidate := narrow_candidate p m in
    if C.check p candidate then inl candidate else inr m.
  Definition refine p n m :=
    match loop_fuel (narrow_step p) n m with
    | inl result => result
    | inr result => result
    end.
End NarrowCode.

Module Narrow (L : WLATTICE) (S : SYSTEM L) (C : CHECK L S) <: NARROW L S C.
  Include NarrowCode L S C.
  Include NARROW_SPEC L S C.

  (** An empty contribution store reads as bottom. *)
  Lemma look_or_empty : forall x,
    look_or S.key_code L.bot Empty x = L.bot.
  Proof.
    intro x; unfold look_or.
    change (match PTrie.get (S.key_code x) (@PTrie.empty (S.key * L.t)) with
      | Some (_, a) => a | None => L.bot end = L.bot).
    now rewrite PTrie.get_empty.
  Qed.

  (** Setting a key changes exactly the lookup at its code. *)
  Lemma look_or_set : forall m y a x,
    look_or S.key_code L.bot (PTrieCode.set (S.key_code y) (y, a) m) x =
      if Pos.eqb (S.key_code y) (S.key_code x) then a
      else look_or S.key_code L.bot m x.
  Proof.
    intros m y a x; unfold look_or.
    change (match PTrie.get (S.key_code x) (PTrie.set (S.key_code y) (y, a) m) with
      | Some (_, b) => b | None => L.bot end =
      if Pos.eqb (S.key_code y) (S.key_code x) then a
      else match PTrie.get (S.key_code x) m with
        | Some (_, b) => b | None => L.bot end).
    destruct (Pos.eqb (S.key_code y) (S.key_code x)) eqn:Heq.
    - apply Pos.eqb_eq in Heq; now rewrite Heq, PTrie.get_set_same.
    - apply Pos.eqb_neq in Heq; rewrite PTrie.get_set_other; [reflexivity|congruence].
  Qed.

  (** Collecting one output joins only at its key. *)
  Lemma collect_one_spec : forall sums y a x,
    look_or S.key_code L.bot (collect_one sums (y, a)) x =
      if Pos.eqb (S.key_code y) (S.key_code x)
      then L.join (look_or S.key_code L.bot sums x) a
      else look_or S.key_code L.bot sums x.
  Proof.
    intros sums y a x; unfold collect_one; rewrite look_or_set.
    destruct (Pos.eqb (S.key_code y) (S.key_code x)) eqn:Heq; [|reflexivity].
    apply Pos.eqb_eq in Heq; apply S.key_code_inj in Heq; now subst y.
  Qed.

  (** Collecting an output list preserves its filtered join order. *)
  Lemma collect_fold_spec : forall xs sums x,
    look_or S.key_code L.bot (fold_left collect_one xs sums) x =
      fold_left (fun acc yb =>
        if Pos.eqb (S.key_code (fst yb)) (S.key_code x)
        then L.join acc (snd yb) else acc) xs (look_or S.key_code L.bot sums x).
  Proof.
    intro xs; induction xs as [|[y a] xs IH]; intros sums x; cbn [fold_left].
    - reflexivity.
    - now rewrite IH, collect_one_spec.
  Qed.

  (** Collecting rows agrees with the scalar contribution fold at every key. *)
  Lemma collect_rows_spec : forall p m rs sums x,
    look_or S.key_code L.bot (fold_left (collect_row p m) rs sums) x =
      fold_left (fun acc r =>
        match S.eval p r (C.look m) with
        | Some (a, ss) =>
          fold_left (fun acc2 yb =>
            if Pos.eqb (S.key_code (fst yb)) (S.key_code x)
            then L.join acc2 (snd yb) else acc2) ss
            (if Pos.eqb (S.key_code (S.target p r)) (S.key_code x)
             then L.join acc a else acc)
        | None => acc
        end) rs (look_or S.key_code L.bot sums x).
  Proof.
    intros p m rs; induction rs as [|r rs IH]; intros sums x; cbn [fold_left].
    - reflexivity.
    - rewrite IH; unfold collect_row, S.eval.
      destruct (eval_query (S.resume p) (C.look m)
        (Datatypes.S (length (S.deps p r))) (S.start p r)) as [[a ss]|].
      + now rewrite collect_fold_spec.
      + reflexivity.
  Qed.

  (** The collected store represents contributions even without well-formedness. *)
  Lemma eval_all_spec : forall p m x,
    look_or S.key_code L.bot (eval_all p m) x = contrib p m x.
  Proof.
    intros p m x; unfold eval_all, contrib.
    rewrite collect_rows_spec, look_or_empty; reflexivity.
  Qed.

  (** Each candidate write uses the frozen old store and frozen contributions. *)
  Lemma narrow_one_spec : forall old sums acc y x,
    C.look (narrow_one old sums acc y) x =
      if Pos.eqb (S.key_code y) (S.key_code x) then
        (if L.leb (look_or S.key_code L.bot sums x) (C.look old x)
         then L.narrow (C.look old x) (look_or S.key_code L.bot sums x)
         else C.look old x)
      else C.look acc x.
  Proof.
    intros old sums acc y x; rewrite C.look_spec; unfold narrow_one.
    rewrite look_or_set.
    destruct (Pos.eqb (S.key_code y) (S.key_code x)) eqn:Heq.
    - apply Pos.eqb_eq in Heq; apply S.key_code_inj in Heq; now subst y.
    - symmetry; apply C.look_spec.
  Qed.

  (** Repeated candidate writes at one key all install the same frozen value. *)
  Lemma narrow_fold_spec : forall old sums xs acc x,
    C.look (fold_left (narrow_one old sums) xs acc) x =
      if existsb (fun y => Pos.eqb (S.key_code y) (S.key_code x)) xs then
        (if L.leb (look_or S.key_code L.bot sums x) (C.look old x)
         then L.narrow (C.look old x) (look_or S.key_code L.bot sums x)
         else C.look old x)
      else C.look acc x.
  Proof.
    intros old sums xs; induction xs as [|y xs IH]; intros acc x.
    - reflexivity.
    - cbn [fold_left existsb]; rewrite IH, narrow_one_spec.
      destruct (existsb (fun z => Pos.eqb (S.key_code z) (S.key_code x)) xs),
        (Pos.eqb (S.key_code y) (S.key_code x)); reflexivity.
  Qed.

  (** A flattened list contains a matching element exactly when one sublist does. *)
  Lemma existsb_flat_map {A B : Type} (f : A -> list B) (test : B -> bool) :
    forall xs, existsb test (flat_map f xs) = existsb (fun x => existsb test (f x)) xs.
  Proof.
    intro xs; induction xs as [|x xs IH]; cbn [flat_map existsb].
    - reflexivity.
    - now rewrite existsb_app, IH.
  Qed.

  (** Candidate lookup needs no well-formedness premise. *)
  Lemma candidate_lookup : forall p m x,
    C.look (narrow_candidate p m) x =
      if writtenb p x then
        (if L.leb (contrib p m x) (C.look m x)
         then L.narrow (C.look m x) (contrib p m x) else C.look m x)
      else C.look m x.
  Proof.
    intros p m x; unfold narrow_candidate.
    now rewrite narrow_fold_spec, existsb_flat_map, eval_all_spec.
  Qed.

  (** The guarded candidate always lies below its input store. *)
  Lemma candidate_below : forall p m x,
    L.leb (C.look (narrow_candidate p m) x) (C.look m x) = true.
  Proof.
    intros p m x; rewrite candidate_lookup.
    destruct (writtenb p x); [|apply L.leb_refl].
    destruct (L.leb (contrib p m x) (C.look m x)) eqn:Hguard; [|apply L.leb_refl].
    exact (proj2 (L.narrow_between (C.look m x) (contrib p m x) Hguard)).
  Qed.

  (** A value below both the old lookup and the aggregate remains below the candidate. *)
  Lemma candidate_keeps_bound : forall p m x a,
    L.leb a (C.look m x) = true -> L.leb a (contrib p m x) = true ->
    L.leb a (C.look (narrow_candidate p m) x) = true.
  Proof.
    intros p m x a Hold Hsum; rewrite candidate_lookup.
    destruct (writtenb p x); [|exact Hold].
    destruct (L.leb (contrib p m x) (C.look m x)) eqn:Hguard; [|exact Hold].
    eapply L.leb_trans; [exact Hsum|].
    exact (proj1 (L.narrow_between (C.look m x) (contrib p m x) Hguard)).
  Qed.

  (** A fold of increasing updates remains above its initial observation. *)
  Lemma fold_left_above {A B : Type} (step : A -> B -> A) (value : A -> L.t) :
    (forall acc y, L.leb (value acc) (value (step acc y)) = true) ->
    forall xs acc, L.leb (value acc) (value (fold_left step xs acc)) = true.
  Proof.
    intros Hstep xs; induction xs as [|y xs IH]; intro acc; cbn [fold_left].
    - apply L.leb_refl.
    - eapply L.leb_trans; [apply Hstep|apply IH].
  Qed.

  (** A bound established by any listed update survives the remaining increasing updates. *)
  Lemma fold_left_member_bound {A B : Type} (step : A -> B -> A) (value : A -> L.t) :
    (forall acc y, L.leb (value acc) (value (step acc y)) = true) ->
    forall xs acc y a, In y xs ->
    (forall before, L.leb a (value (step before y)) = true) ->
    L.leb a (value (fold_left step xs acc)) = true.
  Proof.
    intros Hstep xs; induction xs as [|z xs IH]; intros acc y a Hin Hbound.
    - contradiction.
    - cbn [fold_left]; destruct Hin as [Heq|Hin].
      + subst z; eapply L.leb_trans; [apply Hbound|].
        apply fold_left_above; exact Hstep.
      + eapply IH; [exact Hin|exact Hbound].
  Qed.

  (** Every collected output preserves all previous aggregate bounds. *)
  Lemma collect_one_above : forall sums xa x,
    L.leb (look_or S.key_code L.bot sums x)
      (look_or S.key_code L.bot (collect_one sums xa) x) = true.
  Proof.
    intros sums [y a] x; rewrite collect_one_spec.
    destruct (Pos.eqb (S.key_code y) (S.key_code x));
      [apply L.join_ub_l|apply L.leb_refl].
  Qed.

  (** The newly collected value is below its updated aggregate. *)
  Lemma collect_one_bound : forall sums x a,
    L.leb a (look_or S.key_code L.bot (collect_one sums (x, a)) x) = true.
  Proof.
    intros sums x a; rewrite collect_one_spec, Pos.eqb_refl; apply L.join_ub_r.
  Qed.

  (** Collecting a list preserves the previous aggregate at every key. *)
  Lemma collect_fold_above : forall xs sums x,
    L.leb (look_or S.key_code L.bot sums x)
      (look_or S.key_code L.bot (fold_left collect_one xs sums) x) = true.
  Proof.
    intros xs sums x.
    apply (fold_left_above collect_one (fun acc => look_or S.key_code L.bot acc x)).
    intros; apply collect_one_above.
  Qed.

  (** Each output in a list lies below its final aggregate. *)
  Lemma collect_fold_bound : forall xs sums x a, In (x, a) xs ->
    L.leb a (look_or S.key_code L.bot (fold_left collect_one xs sums) x) = true.
  Proof.
    intros xs sums x a Hin.
    eapply (fold_left_member_bound collect_one
      (fun acc => look_or S.key_code L.bot acc x)) with (y := (x, a)).
    - intros; apply collect_one_above.
    - exact Hin.
    - intro initial; apply collect_one_bound.
  Qed.

  (** Collecting a row preserves every previous aggregate bound. *)
  Lemma collect_row_above : forall p m sums r x,
    L.leb (look_or S.key_code L.bot sums x)
      (look_or S.key_code L.bot (collect_row p m sums r) x) = true.
  Proof.
    intros p m sums r x; unfold collect_row.
    destruct (eval_query (S.resume p) (C.look m)
      (Datatypes.S (length (S.deps p r))) (S.start p r)) as [[a ss]|].
    - apply collect_fold_above.
    - apply L.leb_refl.
  Qed.

  (** A successful row contributes an upper bound for each actual output. *)
  Lemma collect_row_bound : forall p m sums r a ss x b,
    S.eval p r (C.look m) = Some (a, ss) ->
    In (x, b) ((S.target p r, a) :: ss) ->
    L.leb b (look_or S.key_code L.bot (collect_row p m sums r) x) = true.
  Proof.
    intros p m sums r a ss x b Heval Hin; unfold collect_row.
    unfold S.eval in Heval; rewrite Heval; now apply collect_fold_bound.
  Qed.

  (** Every output of a listed row lies below the program's aggregate at its key. *)
  Lemma eval_all_bound : forall p m r a ss x b,
    In r (S.rows p) -> S.eval p r (C.look m) = Some (a, ss) ->
    In (x, b) ((S.target p r, a) :: ss) -> L.leb b (contrib p m x) = true.
  Proof.
    intros p m r a ss x b Hrow Heval Hin; rewrite <- eval_all_spec; unfold eval_all.
    eapply (fold_left_member_bound (collect_row p m)
      (fun acc => look_or S.key_code L.bot acc x)) with (y := r).
    - intros; apply collect_row_above.
    - exact Hrow.
    - intro initial; eapply collect_row_bound; [exact Heval|exact Hin].
  Qed.

  (** The candidate still bounds the old outputs of every already accepted row. *)
  Lemma candidate_row_old : forall p m r, In r (S.rows p) ->
    row_ok L.leb (C.look m) (S.target p r) (S.eval p r (C.look m)) = true ->
    row_ok L.leb (C.look (narrow_candidate p m)) (S.target p r)
      (S.eval p r (C.look m)) = true.
  Proof.
    intros p m r Hrow Hpost.
    destruct (S.eval p r (C.look m)) as [[a ss]|] eqn:Heval; [|discriminate].
    cbn [row_ok] in Hpost |- *; apply andb_true_iff in Hpost as [Hmain Hsides].
    apply andb_true_iff; split.
    - apply candidate_keeps_bound; [exact Hmain|].
      eapply eval_all_bound; [exact Hrow|exact Heval|now left].
    - apply forallb_forall; intros [x b] Hin; apply candidate_keeps_bound.
      + apply forallb_forall with (x := (x, b)) in Hsides; [exact Hsides|exact Hin].
      + eapply eval_all_bound; [exact Hrow|exact Heval|now right].
  Qed.

  (** Pointwise smaller ordered side outputs retain all lookup bounds. *)
  Lemma sides_ok_out_leb : forall ss ts (look : S.key -> L.t),
    Forall2 (fun xa yb => fst xa = fst yb /\ L.leb (snd xa) (snd yb) = true) ss ts ->
    forallb (fun xa => L.leb (snd xa) (look (fst xa))) ts = true ->
    forallb (fun xa => L.leb (snd xa) (look (fst xa))) ss = true.
  Proof.
    intros ss ts look Hsides; induction Hsides as [|xa yb ss ts Hpair Hsides IH];
      intro Hbound; [reflexivity|].
    cbn [forallb] in Hbound |- *; apply andb_true_iff in Hbound as [Hhead Htail].
    destruct Hpair as [Hkey Hle]; apply andb_true_iff; split.
    - eapply L.leb_trans; [exact Hle|now rewrite Hkey].
    - now apply IH.
  Qed.

  (** Decreasing a successful output preserves its acceptance against a fixed lookup. *)
  Lemma row_ok_out_leb : forall (look : S.key -> L.t) x left right,
    out_leb L.leb left right -> row_ok L.leb look x right = true ->
    row_ok L.leb look x left = true.
  Proof.
    intros look x [[a ss]|] [[b ts]|] Hout Hrow; try contradiction.
    destruct Hout as [Hle Hsides]; cbn [row_ok] in Hrow |- *.
    apply andb_true_iff in Hrow as [Hmain Htail]; apply andb_true_iff; split.
    - eapply L.leb_trans; [exact Hle|exact Hmain].
    - eapply sides_ok_out_leb; [exact Hsides|exact Htail].
  Qed.

  (** The candidate narrows exactly its declared writes against frozen contributions. *)
  Lemma narrow_candidate_spec : forall p m x, S.wf p ->
    C.look (narrow_candidate p m) x =
      if writtenb p x then
        (let a := C.look m x in let b := contrib p m x in
         if L.leb b a then L.narrow a b else a)
      else C.look m x.
  Proof.
    intros p m x Hwf; apply candidate_lookup.
  Qed.

  (** A pass accepts the candidate precisely when its check succeeds. *)
  Lemma narrow_pass_spec : forall p m,
    narrow_pass p m = if C.check p (narrow_candidate p m) then narrow_candidate p m else m.
  Proof.
    reflexivity.
  Qed.

  (** The always-continuing loop computes the requested iteration. *)
  Lemma refine_loop_spec : forall p n m,
    loop_fuel (fun st => @inl (kmap S.key L.t) unit (narrow_pass p st)) n m =
      inl (Nat.iter n (narrow_pass p) m).
  Proof.
    intros p n; induction n as [|n IH]; intro m; [reflexivity|].
    cbn [loop_fuel]; now rewrite IH, Nat.iter_succ_r.
  Qed.

  (** Once a candidate is rejected, every further pass keeps the same store. *)
  Lemma narrow_pass_rejected_iter : forall p n m,
    C.check p (narrow_candidate p m) = false -> Nat.iter n (narrow_pass p) m = m.
  Proof.
    intros p n; induction n as [|n IH]; intros m Hcheck.
    - reflexivity.
    - rewrite Nat.iter_succ, IH by exact Hcheck.
      unfold narrow_pass; now rewrite Hcheck.
  Qed.

  (** Refinement performs exactly the requested number of checked passes. *)
  Lemma refine_spec : forall p n m, refine p n m = Nat.iter n (narrow_pass p) m.
  Proof.
    intros p n; induction n as [|n IH]; intro m; [reflexivity|].
    rewrite Nat.iter_succ_r, narrow_pass_spec.
    unfold refine at 1; cbn [loop_fuel]; unfold narrow_step at 1.
    destruct (C.check p (narrow_candidate p m)) eqn:Hcheck.
    - apply IH.
    - symmetry; now apply narrow_pass_rejected_iter.
  Qed.

  (** Accepted candidates and rejected passes both preserve a post-solution. *)
  Lemma narrow_pass_post : forall p m, S.post_solution p (C.look m) ->
    S.post_solution p (C.look (narrow_pass p m)).
  Proof.
    intros p m Hpost; unfold narrow_pass.
    destruct (C.check p (narrow_candidate p m)) eqn:Hcheck; [|exact Hpost].
    now apply C.check_sound.
  Qed.

  (** A checked pass lowers every lookup even when its candidate is rejected. *)
  Lemma narrow_pass_below : forall p m x,
    L.leb (C.look (narrow_pass p m) x) (C.look m x) = true.
  Proof.
    intros p m x; unfold narrow_pass; destruct (C.check p (narrow_candidate p m)).
    - apply candidate_below.
    - apply L.leb_refl.
  Qed.

  (** Monotonicity makes the guarded candidate of a post-solution pass every row. *)
  Lemma narrow_pass_exact_mono : forall p, S.monotone p -> forall m,
    S.post_solution p (C.look m) -> C.check p (narrow_candidate p m) = true.
  Proof.
    intros p Hmono m Hpost; rewrite C.check_spec; apply C.check_rows_iff.
    intros r Hrow; eapply row_ok_out_leb with (right := S.eval p r (C.look m)).
    - apply Hmono; [exact Hrow|intro x; apply candidate_below].
    - apply candidate_row_old; [exact Hrow|now apply Hpost].
  Qed.

  (** Repeated checked passes preserve the original post-solution property. *)
  Lemma refine_post : forall p n m, S.post_solution p (C.look m) ->
    S.post_solution p (C.look (refine p n m)).
  Proof.
    intros p n m Hpost; rewrite refine_spec; induction n as [|n IH]; cbn [Nat.iter].
    - exact Hpost.
    - now apply narrow_pass_post.
  Qed.

  (** Repeated checked passes stay below the original store at every key. *)
  Lemma refine_below : forall p n m x,
    L.leb (C.look (refine p n m) x) (C.look m x) = true.
  Proof.
    intros p n m x; rewrite refine_spec; induction n as [|n IH]; cbn [Nat.iter].
    - apply L.leb_refl.
    - eapply L.leb_trans; [apply narrow_pass_below|exact IH].
  Qed.
End Narrow.

Module NarrowT (L : WLATTICE_T) (S : SYSTEM_T L) (C : CHECK_T L S) (B : BUDGET L S)
    <: NARROW_T L S C B.
  Include Narrow L S C.
  TimeFun collect_one.
  TimeFun collect_row.
  TimeFun eval_all.
  TimeFun narrow_one.
  TimeFun narrow_candidate.
  TimeFun narrow_pass.
  TimeFun narrow_step.
  TimeFun refine.

  Definition c_base : N := (C.c_chk + S.c_sys + PTrieT.c_trie + 1)%N.
  Definition c_collect : N := (16 * c_base)%N.
  Definition c_row : N := (64 * c_base)%N.
  Definition c_pass : N := (256 * c_base)%N.
  Definition c_nar : N := (512 * c_base)%N.
  Definition pass_work (p : S.prog) : N :=
    (N.of_nat ((fold_right Nat.add 0
      (List.map (fun r => length (S.deps p r) + length (S.sides p r) + 1) (S.rows p)) + 1)%nat) *
    (S.row_work p (B.vsize p) + N.of_nat (S.kw p) +
      L.c_lat * N.of_nat (B.vsize p + 1) + 1))%N.

  Definition row_weight (p : S.prog) (r : S.row) : nat :=
    length (S.deps p r) + length (S.sides p r) + 1.
  Definition row_unit (p : S.prog) : N :=
    (S.row_work p (B.vsize p) + N.of_nat (S.kw p) +
      L.c_lat * N.of_nat (B.vsize p + 1) + 1)%N.
  Definition store_inv (p : S.prog) (m : kmap S.key L.t) : Prop :=
    forall x, B.inv p (C.look m x).

  (** Collection keeps the budget invariant at every intermediate store. *)
  Lemma collect_one_inv : forall p sums x a, store_inv p sums -> B.inv p a ->
    store_inv p (collect_one sums (x, a)).
  Proof.
    intros p sums x a Hsums Ha y.
    rewrite C.look_spec, collect_one_spec, <- C.look_spec.
    destruct (Pos.eqb (S.key_code x) (S.key_code y)); [apply B.inv_join|]; auto.
  Qed.

  (** A list of invariant outputs can be collected in occurrence order. *)
  Lemma collect_fold_inv : forall p xs sums,
    Forall (fun xa => B.inv p (snd xa)) xs -> store_inv p sums ->
    store_inv p (fold_left collect_one xs sums).
  Proof.
    intros p xs; induction xs as [|[x a] xs IH]; intros sums Hxs Hsums.
    - exact Hsums.
    - inversion Hxs as [|xa tail Ha Htail]; subst.
      cbn [fold_left]; apply IH; [exact Htail|].
      apply collect_one_inv; assumption.
  Qed.

  (** A listed row supplies invariant primary and side outputs. *)
  Lemma collect_row_inv : forall p m sums r, S.wf p -> In r (S.rows p) ->
    store_inv p m -> store_inv p sums -> store_inv p (collect_row p m sums r).
  Proof.
    intros p m sums r Hwf Hr Hm Hsums; unfold collect_row.
    fold (S.eval p r (C.look m)).
    destruct (S.eval p r (C.look m)) as [[a ss]|] eqn:Heval.
    - change (store_inv p (fold_left collect_one ((S.target p r, a) :: ss) sums)).
      destruct (B.inv_rows p r (C.look m) a ss Hwf Hr Hm Heval) as [Ha Hss].
      apply collect_fold_inv; [now constructor|exact Hsums].
    - exact Hsums.
  Qed.

  (** Row collection preserves the invariant for each prefix of the row list. *)
  Lemma collect_rows_inv : forall p m rs sums, S.wf p ->
    (forall r, In r rs -> In r (S.rows p)) -> store_inv p m -> store_inv p sums ->
    store_inv p (fold_left (collect_row p m) rs sums).
  Proof.
    intros p m rs; induction rs as [|r rs IH]; intros sums Hwf Hrows Hm Hsums.
    - exact Hsums.
    - cbn [fold_left]; apply IH.
      + exact Hwf.
      + intros r1 Hr1; apply Hrows; now right.
      + exact Hm.
      + apply collect_row_inv; [exact Hwf|apply Hrows; now left|exact Hm|exact Hsums].
  Qed.

  (** Aggregation starts at bottom and keeps every accumulated value in budget. *)
  Lemma eval_all_inv : forall p m, S.wf p -> store_inv p m -> store_inv p (eval_all p m).
  Proof.
    intros p m Hwf Hm; unfold eval_all.
    apply collect_rows_inv; auto.
    intro x; rewrite C.look_spec, look_or_empty; apply B.inv_bot.
  Qed.

  (** A candidate write keeps the invariant in its frozen operands and output store. *)
  Lemma narrow_one_inv : forall p old sums acc x,
    store_inv p old -> store_inv p sums -> store_inv p acc ->
    store_inv p (narrow_one old sums acc x).
  Proof.
    intros p old sums acc x Hold Hsums Hacc y; rewrite narrow_one_spec.
    rewrite <- C.look_spec.
    destruct (Pos.eqb (S.key_code x) (S.key_code y)); [|apply Hacc].
    destruct (L.leb (C.look sums y) (C.look old y)); [apply B.inv_narrow|]; auto.
  Qed.

  (** Candidate construction changes only to invariant narrowed values. *)
  Lemma narrow_candidate_inv : forall p m, S.wf p -> store_inv p m ->
    store_inv p (narrow_candidate p m).
  Proof.
    intros p m Hwf Hm.
    pose proof (eval_all_inv p m Hwf Hm) as Hsums.
    unfold narrow_candidate.
    assert (Hfold : forall xs acc, store_inv p acc ->
      store_inv p (fold_left (narrow_one m (eval_all p m)) xs acc)).
    { intro xs; induction xs as [|x xs IH]; intros acc1 Hacc.
      - exact Hacc.
      - cbn [fold_left]; apply IH; now apply narrow_one_inv. }
    apply Hfold; exact Hm.
  Qed.

  (** Checking either keeps the invariant candidate or returns the invariant input. *)
  Lemma narrow_pass_inv : forall p m, S.wf p -> store_inv p m ->
    store_inv p (narrow_pass p m).
  Proof.
    intros p m Hwf Hm; unfold narrow_pass.
    destruct (C.check p (narrow_candidate p m)); [now apply narrow_candidate_inv|exact Hm].
  Qed.

  (** An invariant store supplies the value-size bound used by the system clock. *)
  Lemma store_size : forall p m, store_inv p m ->
    forall x, L.size (C.look m x) <= B.vsize p.
  Proof.
    intros p m Hm x; now apply B.size_le.
  Qed.

  (** Every row unit pays for one call and for a declared key traversal. *)
  Lemma row_unit_bounds : forall p,
    (1 <= row_unit p)%N /\
    (N.of_nat (S.kw p + 1) <= row_unit p)%N /\
    (L.c_lat * N.of_nat (B.vsize p + 1) <= row_unit p)%N /\
    (S.row_work p 0 + 1 <= row_unit p)%N.
  Proof.
    intro p; pose proof (S.row_work_mono p 0 (B.vsize p) ltac:(lia)).
    unfold row_unit; rewrite Nat2N.inj_add; repeat split; nia.
  Qed.

  (** Raw contribution lookup pays for encoding and trie traversal. *)
  Lemma T_raw_look_le : forall m x,
    (T_look_or S.key_code S.T_key_code L.bot m x <=
      (S.c_sys + PTrieT.c_trie + 2) * N.of_nat (S.key_bits x + 1))%N.
  Proof.
    intros m x; pose proof (S.T_key_code_le x) as Hcode.
    pose proof (PTrieT.T_get_le (S.key * L.t) (S.key_code x) m) as Hget.
    unfold T_look_or, PTrieT.T_get in *; unfold S.key_bits in *.
    rewrite !Nat2N.inj_add in *; time_cbn_all; nia.
  Qed.

  (** A declared key traversal fits one row unit. *)
  Lemma key_unit_le : forall p x, S.key_bits x <= S.kw p ->
    (N.of_nat (S.key_bits x + 1) <= row_unit p)%N.
  Proof.
    intros p x Hbits; destruct (row_unit_bounds p) as [_ [Hkey _]].
    eapply N.le_trans; [|exact Hkey]; lia.
  Qed.

  (** A binary lattice operation on invariant values fits two value budgets. *)
  Lemma value_cost_le : forall p a b t, B.inv p a -> B.inv p b ->
    (t <= L.c_lat * N.of_nat (L.size a + L.size b + 1))%N ->
    (t <= 2 * row_unit p)%N.
  Proof.
    intros p a b t Ha Hb Htime.
    pose proof (B.size_le p a Ha) as Hsizea.
    pose proof (B.size_le p b Hb) as Hsizeb.
    destruct (row_unit_bounds p) as [_ [_ [Hvalue _]]].
    assert (Hsizes : (N.of_nat (L.size a + L.size b + 1) <=
      2 * N.of_nat (B.vsize p + 1))%N) by lia.
    eapply N.le_trans; [exact Htime|].
    eapply N.le_trans; [apply N.mul_le_mono_l; exact Hsizes|].
    replace (L.c_lat * (2 * N.of_nat (B.vsize p + 1)))%N with
      (2 * (L.c_lat * N.of_nat (B.vsize p + 1)))%N by ring.
    now apply N.mul_le_mono_l.
  Qed.

  (** Collecting one output charges its lookup, join and single trie write. *)
  Lemma T_collect_one_le : forall p sums x a, store_inv p sums -> B.inv p a ->
    S.key_bits x <= S.kw p ->
    (T_collect_one sums (x, a) <= c_collect * row_unit p)%N.
  Proof.
    intros p sums x a Hsums Ha Hbits.
    pose proof (key_unit_le p x Hbits) as Hkey_unit.
    destruct (row_unit_bounds p) as [Hunit _].
    assert (Hcode : (S.T_key_code x <= S.c_sys * row_unit p)%N).
    { eapply N.le_trans; [apply S.T_key_code_le|].
      now apply N.mul_le_mono_l. }
    assert (Hlook : (T_look_or S.key_code S.T_key_code L.bot sums x <=
      (S.c_sys + PTrieT.c_trie + 2) * row_unit p)%N).
    { eapply N.le_trans; [apply T_raw_look_le|].
      now apply N.mul_le_mono_l. }
    assert (Hjoin : (L.T_join (look_or S.key_code L.bot sums x) a <=
      2 * row_unit p)%N).
    { apply (value_cost_le p (look_or S.key_code L.bot sums x) a);
        [rewrite <- C.look_spec; apply Hsums|exact Ha|].
      apply L.T_join_le. }
    assert (Hset : (PTrieT.T_set (S.key_code x)
      (x, L.join (look_or S.key_code L.bot sums x) a) sums <=
      PTrieT.c_trie * row_unit p)%N).
    { eapply N.le_trans; [apply PTrieT.T_set_le|].
      now apply N.mul_le_mono_l. }
    unfold T_collect_one, c_collect, c_base.
    time_simpl; time_cbn.
    change (fun y : S.key => S.T_key_code y) with S.T_key_code.
    change (@PTrieCode.T_set (S.key * L.t)) with (@PTrieT.T_set (S.key * L.t)).
    clear -Hcode Hlook Hjoin Hset Hunit; nia.
  Qed.

  (** One candidate write charges the frozen lookups, guard, narrowing and insertion. *)
  Lemma T_narrow_one_le : forall p old sums acc x,
    store_inv p old -> store_inv p sums -> S.key_bits x <= S.kw p ->
    (T_narrow_one old sums acc x <= c_collect * row_unit p)%N.
  Proof.
    intros p old sums acc x Hold Hsums Hbits.
    pose proof (key_unit_le p x Hbits) as Hkey_unit.
    destruct (row_unit_bounds p) as [Hunit _].
    assert (Hcode : (S.T_key_code x <= S.c_sys * row_unit p)%N).
    { eapply N.le_trans; [apply S.T_key_code_le|].
      now apply N.mul_le_mono_l. }
    assert (Hsum_look : (T_look_or S.key_code S.T_key_code L.bot sums x <=
      (S.c_sys + PTrieT.c_trie + 2) * row_unit p)%N).
    { eapply N.le_trans; [apply T_raw_look_le|].
      now apply N.mul_le_mono_l. }
    assert (Hold_look : (C.T_look old x <= C.c_chk * row_unit p)%N).
    { eapply N.le_trans; [apply C.T_look_le|].
      now apply N.mul_le_mono_l. }
    assert (Hsum : B.inv p (look_or S.key_code L.bot sums x)).
    { rewrite <- C.look_spec; apply Hsums. }
    pose proof (value_cost_le p _ _ _ Hsum (Hold x)
      (L.T_leb_le (look_or S.key_code L.bot sums x) (C.look old x))) as Hleb.
    pose proof (value_cost_le p _ _ _ (Hold x) Hsum
      (L.T_narrow_le (C.look old x) (look_or S.key_code L.bot sums x))) as Hnarrow.
    assert (Hset : forall a, (PTrieT.T_set (S.key_code x) (x, a) acc <=
      PTrieT.c_trie * row_unit p)%N).
    { intro a; eapply N.le_trans; [apply PTrieT.T_set_le|].
      now apply N.mul_le_mono_l. }
    unfold T_narrow_one, c_collect, c_base.
    change (fun y : S.key => S.T_key_code y) with S.T_key_code.
    change (@PTrieCode.T_set (S.key * L.t)) with (@PTrieT.T_set (S.key * L.t)).
    destruct (L.leb (look_or S.key_code L.bot sums x) (C.look old x)).
    - specialize (Hset (L.narrow (C.look old x) (look_or S.key_code L.bot sums x))).
      time_simpl; time_cbn.
      clear -Hcode Hsum_look Hold_look Hleb Hnarrow Hset Hunit; nia.
    - specialize (Hset (C.look old x)); time_simpl; time_cbn.
      clear -Hcode Hsum_look Hold_look Hleb Hnarrow Hset Hunit; nia.
  Qed.

  (** A constant callback budget sums once for every list occurrence. *)
  Lemma fold_time_const {A : Type} : forall (xs : list A) t,
    fold_right (fun _ total => t + 2 + total)%N 1%N xs =
      ((t + 2) * N.of_nat (length xs) + 1)%N.
  Proof.
    intro xs; induction xs as [|x xs IH]; intro t; time_cbn.
    - lia.
    - rewrite IH; nia.
  Qed.

  (** Collection charges every output and retains the invariant between callbacks. *)
  Lemma T_collect_fold_le : forall p xs sums,
    Forall (fun xa => B.inv p (snd xa) /\ S.key_bits (fst xa) <= S.kw p) xs ->
    store_inv p sums ->
    (List.T_fold_left collect_one T_collect_one xs sums <=
      (c_collect * row_unit p + 2) * N.of_nat (length xs) + 1)%N.
  Proof.
    intros p xs sums Hxs Hsums; rewrite Forall_forall in Hxs.
    assert (Hstep : forall st xa, store_inv p st -> In xa xs ->
      store_inv p (collect_one st xa) /\
      (T_collect_one st xa <= c_collect * row_unit p)%N).
    { intros st [x a] Hst Hin; destruct (Hxs (x, a) Hin) as [Ha Hbits].
      split; [apply collect_one_inv|apply T_collect_one_le]; assumption. }
    destruct (fold_left_inv_time collect_one T_collect_one (store_inv p)
      (fun _ => c_collect * row_unit p)%N xs sums Hsums Hstep) as [_ Htime].
    now rewrite fold_time_const in Htime.
  Qed.

  (** Reachable query frames and declared dependency keys bound the evaluator clock. *)
  Lemma T_eval_le : forall p m r, S.wf p -> In r (S.rows p) -> store_inv p m ->
    (T_eval_query (S.resume p) (S.T_resume p) (C.look m) (C.T_look m)
      (Datatypes.S (length (S.deps p r))) (S.start p r) <=
      20 * (C.c_chk + S.c_sys + 1) * N.of_nat (row_weight p r) * row_unit p)%N.
  Proof.
    intros p m r Hwf Hr Hm; pose proof (store_size p m Hm) as Hsize.
    destruct (S.eval p r (C.look m)) as [[a ss]|] eqn:Heval.
    2: { exfalso; exact (S.eval_total p r (C.look m) Hwf Hr Heval). }
    pose proof (S.sides_count p r (C.look m) a ss Hwf Hr Heval) as Hcount.
    assert (Hread : forall n q acc x f,
      loop_fuel (eval_step (S.resume p) (C.look m)) n (S.start p r, nil) = inl (q, acc) ->
      fst (peel q acc) = inr (x, f) ->
      (C.T_look m x + S.T_resume p f (C.look m x) <=
        (C.c_chk + S.c_sys) * row_unit p)%N).
    { intros n q acc x f Hprefix Hask.
      pose proof (S.asks_within p r (C.look m) n q acc x f Hwf Hr Hprefix Hask) as Hdep.
      assert (Hbits : S.key_bits x <= S.kw p).
      { apply (S.key_bits_le p r x Hwf Hr); apply in_or_app; now right. }
      pose proof (C.T_look_le m x) as Hlook.
      pose proof (S.T_resume_le p r (C.look m) (B.vsize p) n q acc x f
        Hwf Hr Hsize Hprefix Hask) as Hresume.
      assert (HbitsN : (N.of_nat (S.key_bits x) <= N.of_nat (S.kw p))%N) by lia.
      unfold row_unit; rewrite Nat2N.inj_add in Hlook; time_cbn; nia. }
    pose proof (T_eval_query_le (S.resume p) (S.T_resume p) (C.look m) (C.T_look m)
      (Datatypes.S (length (S.deps p r))) (S.start p r) a ss
      ((C.c_chk + S.c_sys) * row_unit p)%N Heval Hread) as Heval_cost.
    assert (HcountN : (N.of_nat (length ss) <= N.of_nat (length (S.sides p r)))%N)
      by lia.
    destruct (row_unit_bounds p) as [Hunit _].
    unfold row_weight; rewrite !Nat2N.inj_add, !Nat2N.inj_succ in *.
    clear -Heval_cost HcountN Hunit; nia.
  Qed.

  (** A successful listed row returns invariant outputs at budgeted keys. *)
  Lemma row_outputs : forall p m r a ss, S.wf p -> In r (S.rows p) -> store_inv p m ->
    S.eval p r (C.look m) = Some (a, ss) ->
    Forall (fun xa => B.inv p (snd xa) /\ S.key_bits (fst xa) <= S.kw p)
      ((S.target p r, a) :: ss).
  Proof.
    intros p m r a ss Hwf Hr Hm Heval.
    destruct (B.inv_rows p r (C.look m) a ss Hwf Hr Hm Heval) as [Ha Hss].
    constructor.
    - split; [exact Ha|].
      apply (S.key_bits_le p r (S.target p r) Hwf Hr).
      unfold S.writes; apply in_or_app; left; now left.
    - rewrite Forall_forall; intros [x b] Hin; split.
      + rewrite Forall_forall in Hss; exact (Hss (x, b) Hin).
      + apply (S.key_bits_le p r x Hwf Hr).
        unfold S.writes; apply in_or_app; left; right.
        exact (S.sides_within p r (C.look m) a ss x b Hwf Hr Heval Hin).
  Qed.

  (** One row pays for evaluation and each actual output collection. *)
  Lemma T_collect_row_le : forall p m sums r, S.wf p -> In r (S.rows p) ->
    store_inv p m -> store_inv p sums ->
    (T_collect_row p m sums r <= c_row * N.of_nat (row_weight p r) * row_unit p)%N.
  Proof.
    intros p m sums r Hwf Hr Hm Hsums.
    pose proof (T_eval_le p m r Hwf Hr Hm) as Heval_cost.
    pose proof (S.T_target_le p r Hwf Hr) as Htarget.
    pose proof (S.T_start_le p r Hwf Hr) as Hstart.
    pose proof (S.T_deps_le p r Hwf Hr) as Hdeps.
    pose proof (Datatypes.T_length_le (S.deps p r)) as Hlength.
    destruct (S.eval p r (C.look m)) as [[a ss]|] eqn:Heval.
    2: { exfalso; exact (S.eval_total p r (C.look m) Hwf Hr Heval). }
    pose proof (row_outputs p m r a ss Hwf Hr Hm Heval) as Houtputs.
    pose proof (T_collect_fold_le p ((S.target p r, a) :: ss) sums Houtputs Hsums)
      as Hcollect.
    pose proof (S.sides_count p r (C.look m) a ss Hwf Hr Heval) as Hcount.
    set (u := row_unit p) in *.
    set (d := N.of_nat (row_weight p r)) in *.
    set (chunk := (d * u)%N).
    destruct (row_unit_bounds p) as [Hu [Hkey [_ Hwork]]]; fold u in Hu, Hkey, Hwork.
    assert (Hd : (1 <= d)%N) by (unfold d, row_weight; lia).
    assert (Hdeps_size : (N.of_nat (length (S.deps p r) + 1) <= d)%N)
      by (unfold d, row_weight; lia).
    assert (Houts_size : (N.of_nat (length ((S.target p r, a) :: ss)) <= d)%N).
    { unfold d, row_weight; cbn [length]; lia. }
    assert (Hchunk : (1 <= chunk)%N) by (unfold chunk; clear -Hd Hu; nia).
    assert (Hunit_chunk : (u <= chunk)%N) by (unfold chunk; clear -Hd; nia).
    assert (Hweight_chunk : (d <= chunk)%N) by (unfold chunk; clear -Hu; nia).
    assert (Htarget_bound : (S.T_target p r <= S.c_sys * chunk)%N).
    { eapply N.le_trans; [exact Htarget|].
      apply N.mul_le_mono_l; eapply N.le_trans; eassumption. }
    assert (Hstart_bound : (S.T_start p r <= S.c_sys * chunk)%N).
    { eapply N.le_trans; [exact Hstart|].
      apply N.mul_le_mono_l; eapply N.le_trans; eassumption. }
    assert (Hdeps_bound : (S.T_deps p r <= S.c_sys * chunk)%N).
    { eapply N.le_trans; [exact Hdeps|].
      unfold chunk; rewrite N.mul_assoc.
      apply N.mul_le_mono; [now apply N.mul_le_mono_l|exact Hkey]. }
    assert (Hlength_bound : (Datatypes.T_length (S.deps p r) <= chunk)%N).
    { rewrite Nat2N.inj_add in Hdeps_size; unfold chunk.
      clear -Hlength Hdeps_size Hu; nia. }
    assert (Hcollect_bound : (List.T_fold_left collect_one T_collect_one
      ((S.target p r, a) :: ss) sums <= (c_collect + 3) * chunk)%N).
    { eapply N.le_trans; [exact Hcollect|].
      eapply N.le_trans with (m := ((c_collect * u + 2) * d + 1)%N).
      - apply N.add_le_mono_r; now apply N.mul_le_mono_l.
      - replace ((c_collect * u + 2) * d + 1)%N with
          (c_collect * chunk + 2 * d + 1)%N by (unfold chunk; ring).
        clear -Hweight_chunk Hchunk; nia. }
    replace (20 * (C.c_chk + S.c_sys + 1) * d * u)%N with
      (20 * (C.c_chk + S.c_sys + 1) * chunk)%N in Heval_cost
      by (unfold chunk; ring).
    replace (c_row * d * u)%N with (c_row * chunk)%N by (unfold chunk; ring).
    unfold T_collect_row.
    change (fun f a => S.T_resume p f a) with (S.T_resume p).
    change (fun x => C.T_look m x) with (C.T_look m).
    change (fun st xa => T_collect_one st xa) with T_collect_one.
    fold (S.eval p r (C.look m)); rewrite Heval.
    time_simpl; time_cbn.
    clear -Htarget_bound Hstart_bound Hdeps_bound Hlength_bound Hcollect_bound
      Heval_cost Hchunk.
    unfold c_row, c_collect, c_base in *; nia.
  Qed.

  (** The row weights cover one list node for each row occurrence. *)
  Lemma rows_length_le : forall p rs,
    length rs <= fold_right Nat.add 0 (List.map (row_weight p) rs).
  Proof.
    intros p rs; induction rs as [|r rs IH]; cbn [List.map fold_right length].
    - lia.
    - assert (Hrow : 1 <= row_weight p r) by (unfold row_weight; lia).
      lia.
  Qed.

  (** A weighted callback sum separates row work from list traversal. *)
  Lemma fold_time_weights {A : Type} (weight : A -> nat) : forall xs c u,
    fold_right (fun x total => c * N.of_nat (weight x) * u + 2 + total)%N 1%N xs =
      (c * N.of_nat (fold_right Nat.add 0%nat (List.map weight xs)) * u +
        2 * N.of_nat (length xs) + 1)%N.
  Proof.
    intro xs; induction xs as [|x xs IH]; intros c u; time_cbn.
    - lia.
    - rewrite IH, Nat2N.inj_add; ring.
  Qed.

  (** Row aggregation sums callback work while maintaining the intermediate invariant. *)
  Lemma T_collect_rows_le : forall p m rs sums, S.wf p ->
    (forall r, In r rs -> In r (S.rows p)) -> store_inv p m -> store_inv p sums ->
    (List.T_fold_left (collect_row p m) (T_collect_row p m) rs sums <=
      c_row * N.of_nat (fold_right Nat.add 0%nat (List.map (row_weight p) rs)) * row_unit p +
        2 * N.of_nat (length rs) + 1)%N.
  Proof.
    intros p m rs sums Hwf Hrows Hm Hsums.
    assert (Hstep : forall st r, store_inv p st -> In r rs ->
      store_inv p (collect_row p m st r) /\
      (T_collect_row p m st r <= c_row * N.of_nat (row_weight p r) * row_unit p)%N).
    { intros st r Hst Hr; split; [apply collect_row_inv|apply T_collect_row_le]; auto. }
    destruct (fold_left_inv_time (collect_row p m) (T_collect_row p m) (store_inv p)
      (fun r => c_row * N.of_nat (row_weight p r) * row_unit p)%N
      rs sums Hsums Hstep) as [_ Htime].
    now rewrite fold_time_weights in Htime.
  Qed.

  (** Full aggregation adds the cost of enumerating the source rows. *)
  Lemma T_eval_all_le : forall p m, S.wf p -> store_inv p m ->
    (T_eval_all p m <= (c_row + S.c_sys + 4) * pass_work p)%N.
  Proof.
    intros p m Hwf Hm.
    assert (Hempty : store_inv p Empty).
    { intro x; rewrite C.look_spec, look_or_empty; apply B.inv_bot. }
    pose proof (T_collect_rows_le p m (S.rows p) Empty Hwf
      (fun r Hr => Hr) Hm Hempty) as Hfold.
    pose proof (S.T_rows_le p Hwf) as Hrows.
    pose proof (rows_length_le p (S.rows p)) as Hlength.
    destruct (row_unit_bounds p) as [Hu _].
    unfold T_eval_all.
    change (fun st r => T_collect_row p m st r) with (T_collect_row p m).
    time_simpl; time_cbn.
    unfold pass_work; fold (row_weight p); fold (row_unit p).
    rewrite Nat2N.inj_add in Hrows |- *.
    set (d := N.of_nat (fold_right Nat.add 0 (List.map (row_weight p) (S.rows p)))) in *.
    set (u := row_unit p) in *.
    assert (HlengthN : (N.of_nat (length (S.rows p)) <= d)%N) by (unfold d; lia).
    clear -Hfold Hrows HlengthN Hu; nia.
  Qed.

  (** Declared writes use the same key budget as row evaluation. *)
  Lemma writes_key_bits : forall p x, S.wf p ->
    In x (flat_map (fun r => S.target p r :: S.sides p r) (S.rows p)) ->
    S.key_bits x <= S.kw p.
  Proof.
    intros p x Hwf Hin; rewrite in_flat_map in Hin.
    destruct Hin as [r [Hr Hx]].
    apply (S.key_bits_le p r x Hwf Hr).
    unfold S.writes; apply in_or_app; now left.
  Qed.

  (** The declared write-list length fits the occurrence-weight sum. *)
  Lemma writes_length_le : forall p rs,
    length (flat_map (fun r => S.target p r :: S.sides p r) rs) <=
      fold_right Nat.add 0 (List.map (row_weight p) rs).
  Proof.
    intros p rs; induction rs as [|r rs IH]; cbn [flat_map List.map fold_right].
    - reflexivity.
    - rewrite length_app; cbn [length].
      assert (Hrow : S (length (S.sides p r)) <= row_weight p r)
        by (unfold row_weight; lia).
      lia.
  Qed.

  (** Enumerating one write-list pays for metadata and the appended list cells. *)
  Lemma T_writes_row_le : forall p r tail, S.wf p -> In r (S.rows p) ->
    (1 + (1 + (S.T_target p r + S.T_sides p r)) +
      Datatypes.T_app (S.target p r :: S.sides p r) tail <=
      (2 * S.c_sys + 5) * N.of_nat (row_weight p r) * row_unit p)%N.
  Proof.
    intros p r tail Hwf Hr.
    pose proof (S.T_target_le p r Hwf Hr) as Htarget.
    pose proof (S.T_sides_le p r Hwf Hr) as Hsides.
    pose proof (Datatypes.T_app_le (S.target p r :: S.sides p r) tail) as Happ.
    destruct (row_unit_bounds p) as [Hu [Hkey [_ Hwork]]].
    set (u := row_unit p) in *.
    set (d := N.of_nat (row_weight p r)) in *.
    set (chunk := (d * u)%N).
    assert (Hd : (1 <= d)%N) by (unfold d, row_weight; lia).
    assert (Hlist : (N.of_nat (length (S.sides p r) + 1) <= d)%N)
      by (unfold d, row_weight; lia).
    assert (Hchunk : (1 <= chunk)%N) by (unfold chunk; clear -Hd Hu; nia).
    assert (Hunit_chunk : (u <= chunk)%N) by (unfold chunk; clear -Hd; nia).
    assert (Hweight_chunk : (d <= chunk)%N) by (unfold chunk; clear -Hu; nia).
    assert (Htarget_bound : (S.T_target p r <= S.c_sys * chunk)%N).
    { eapply N.le_trans; [exact Htarget|].
      apply N.mul_le_mono_l; eapply N.le_trans; eassumption. }
    assert (Hsides_bound : (S.T_sides p r <= S.c_sys * chunk)%N).
    { eapply N.le_trans; [exact Hsides|].
      unfold chunk; rewrite N.mul_assoc.
      apply N.mul_le_mono; [now apply N.mul_le_mono_l|exact Hkey]. }
    assert (Happ_bound : (Datatypes.T_app (S.target p r :: S.sides p r) tail <=
      2 * chunk)%N).
    { cbn [length] in Happ; rewrite Nat2N.inj_succ in Happ.
      rewrite Nat2N.inj_add in Hlist.
      clear -Happ Hlist Hweight_chunk Hchunk; lia. }
    replace ((2 * S.c_sys + 5) * d * u)%N with
      ((2 * S.c_sys + 5) * chunk)%N by (unfold chunk; ring).
    clear -Htarget_bound Hsides_bound Happ_bound Hchunk; nia.
  Qed.

  (** Flattening declarations charges each row and each declared side occurrence. *)
  Lemma T_writes_le : forall p rs, S.wf p ->
    (forall r, In r rs -> In r (S.rows p)) ->
    (T_flat_map (fun r => S.target p r :: S.sides p r)
      (fun r => 1 + (S.T_target p r + S.T_sides p r))%N rs <=
      (2 * S.c_sys + 5) *
        N.of_nat (fold_right Nat.add 0%nat (List.map (row_weight p) rs)) * row_unit p + 1)%N.
  Proof.
    intros p rs; induction rs as [|r rs IH]; intros Hwf Hrows.
    - time_step.
    - pose proof (T_writes_row_le p r
        (flat_map (fun r1 => S.target p r1 :: S.sides p r1) rs)
        Hwf (Hrows r (or_introl eq_refl))) as Hrow.
      specialize (IH Hwf (fun r1 Hr1 => Hrows r1 (or_intror Hr1))).
      time_unfold @T_flat_map; time_simpl; time_cbn_all.
      rewrite Nat2N.inj_add.
      clear -Hrow IH; nia.
  Qed.

  (** Candidate writes have a uniform cost on the frozen invariant inputs. *)
  Lemma T_narrow_fold_le : forall p old sums xs acc,
    store_inv p old -> store_inv p sums -> store_inv p acc ->
    (forall x, In x xs -> S.key_bits x <= S.kw p) ->
    (List.T_fold_left (narrow_one old sums) (T_narrow_one old sums) xs acc <=
      (c_collect * row_unit p + 2) * N.of_nat (length xs) + 1)%N.
  Proof.
    intros p old sums xs acc Hold Hsums Hacc Hkeys.
    assert (Hstep : forall st x, store_inv p st -> In x xs ->
      store_inv p (narrow_one old sums st x) /\
      (T_narrow_one old sums st x <= c_collect * row_unit p)%N).
    { intros st x Hst Hx; split.
      - now apply narrow_one_inv.
      - apply T_narrow_one_le; auto. }
    destruct (fold_left_inv_time (narrow_one old sums) (T_narrow_one old sums)
      (store_inv p) (fun _ => c_collect * row_unit p)%N xs acc Hacc Hstep)
      as [_ Htime].
    now rewrite fold_time_const in Htime.
  Qed.

  (** The public pass budget is a positive product of occurrence and row budgets. *)
  Lemma pass_work_eq : forall p,
    pass_work p =
      ((N.of_nat (fold_right Nat.add 0%nat (List.map (row_weight p) (S.rows p))) + 1) *
        row_unit p)%N.
  Proof.
    intro p; unfold pass_work, row_weight, row_unit; rewrite Nat2N.inj_add; reflexivity.
  Qed.

  (** The empty program still pays for the constant work of a pass. *)
  Lemma pass_work_pos : forall p, (1 <= pass_work p)%N.
  Proof.
    intro p; destruct (row_unit_bounds p) as [Hu _]; rewrite pass_work_eq; nia.
  Qed.

  (** Candidate construction combines aggregation, declaration enumeration and frozen writes. *)
  Lemma T_narrow_candidate_le : forall p m, S.wf p -> store_inv p m ->
    (T_narrow_candidate p m <= 128 * c_base * pass_work p)%N.
  Proof.
    intros p m Hwf Hm.
    pose proof (eval_all_inv p m Hwf Hm) as Hsums.
    pose proof (T_eval_all_le p m Hwf Hm) as Heval.
    pose proof (T_writes_le p (S.rows p) Hwf (fun r Hr => Hr)) as Hwrites.
    pose proof (T_narrow_fold_le p m (eval_all p m)
      (flat_map (fun r => S.target p r :: S.sides p r) (S.rows p)) m
      Hm Hsums Hm (fun x Hx => writes_key_bits p x Hwf Hx)) as Hfold.
    pose proof (S.T_rows_le p Hwf) as Hrows.
    pose proof (rows_length_le p (S.rows p)) as Hrows_len.
    pose proof (writes_length_le p (S.rows p)) as Hwrites_len.
    pose proof (pass_work_eq p) as Hwork.
    pose proof (pass_work_pos p) as Hpositive.
    destruct (row_unit_bounds p) as [Hu _].
    set (d := N.of_nat (fold_right Nat.add 0 (List.map (row_weight p) (S.rows p)))) in *.
    set (u := row_unit p) in *.
    set (w := pass_work p) in *.
    assert (HrowsN : (N.of_nat (length (S.rows p)) + 1 <= w)%N).
    { assert (N.of_nat (length (S.rows p)) <= d)%N by (unfold d; lia).
      clear -H Hu Hwork; nia. }
    assert (HwriteN : (N.of_nat
      (length (flat_map (fun r => S.target p r :: S.sides p r) (S.rows p))) <= d)%N)
      by (unfold d; lia).
    assert (Hdu : (d * u <= w)%N) by (clear -Hwork; nia).
    assert (Hd : (d <= w)%N) by (clear -Hwork Hu; nia).
    assert (Hrows_bound : (S.T_rows p <= S.c_sys * w)%N).
    { eapply N.le_trans; [exact Hrows|].
      rewrite Nat2N.inj_add; time_cbn; now apply N.mul_le_mono_l. }
    assert (Hwrites_bound : (T_flat_map (fun r => S.target p r :: S.sides p r)
      (fun r => 1 + (S.T_target p r + S.T_sides p r))%N (S.rows p) <=
      (2 * S.c_sys + 6) * w)%N).
    { assert (Hmul : ((2 * S.c_sys + 5) * (d * u) <=
        (2 * S.c_sys + 5) * w)%N) by now apply N.mul_le_mono_l.
      clear -Hwrites Hmul Hpositive; nia. }
    assert (Hfold_bound : (List.T_fold_left (narrow_one m (eval_all p m))
      (T_narrow_one m (eval_all p m))
      (flat_map (fun r => S.target p r :: S.sides p r) (S.rows p)) m <=
      (c_collect + 3) * w)%N).
    { eapply N.le_trans; [exact Hfold|].
      eapply N.le_trans with (m := ((c_collect * u + 2) * d + 1)%N).
      - apply N.add_le_mono_r; now apply N.mul_le_mono_l.
      - assert (Hmul : (c_collect * (d * u) <= c_collect * w)%N)
          by now apply N.mul_le_mono_l.
        clear -Hmul Hd Hpositive; nia. }
    unfold T_narrow_candidate.
    change (fun st x => T_narrow_one m (eval_all p m) st x)
      with (T_narrow_one m (eval_all p m)).
    time_simpl; time_cbn.
    clear -Heval Hrows_bound Hwrites_bound Hfold_bound Hpositive.
    unfold c_row, c_collect, c_base in *; nia.
  Qed.

  (** A stricter pass estimate reserves room for the refinement loop's own work. *)
  Lemma T_narrow_pass_bound : forall p m, S.wf p -> store_inv p m ->
    (T_narrow_pass p m <= c_pass * pass_work p)%N.
  Proof.
    intros p m Hwf Hm.
    pose proof (T_narrow_candidate_le p m Hwf Hm) as Hcandidate.
    pose proof (narrow_candidate_inv p m Hwf Hm) as Hcandidate_inv.
    pose proof (C.T_check_le p (narrow_candidate p m) (B.vsize p) Hwf
      (store_size p (narrow_candidate p m) Hcandidate_inv)) as Hcheck.
    rewrite <- N.mul_assoc in Hcheck.
    change (C.T_check p (narrow_candidate p m) <= C.c_chk * pass_work p)%N in Hcheck.
    pose proof (pass_work_pos p) as Hpositive.
    unfold T_narrow_pass; time_cbn.
    clear -Hcandidate Hcheck Hpositive; unfold c_pass, c_base in *; nia.
  Qed.

  (** One pass fits a budgeted row sweep. *)
  Lemma T_narrow_pass_le : forall p m, S.wf p ->
    (forall x, B.inv p (C.look m x)) -> (T_narrow_pass p m <= c_nar * pass_work p)%N.
  Proof.
    intros p m Hwf Hm; pose proof (T_narrow_pass_bound p m Hwf Hm) as Hpass.
    unfold c_nar, c_pass in *; nia.
  Qed.

  (** A rejected first pass costs the same for every positive pass budget. *)
  Lemma T_refine_rejected : forall p n m,
    C.check p (narrow_candidate p m) = false ->
    T_refine p (S n) m = T_refine p 1 m.
  Proof.
    intros p n m Hcheck.
    unfold T_refine; time_unfold @T_loop_fuel; unfold narrow_step.
    now rewrite Hcheck.
  Qed.

  (** Accepted callbacks preserve the pass budget, and rejected callbacks end the loop. *)
  Lemma T_refine_loop_le : forall p k m, S.wf p -> store_inv p m ->
    (T_loop_fuel (narrow_step p) (T_narrow_step p) k m <=
      (c_pass * pass_work p + 2) * N.of_nat k + 1)%N.
  Proof.
    intros p k; induction k as [|k IH]; intros m Hwf Hm.
    - time_step.
    - pose proof (T_narrow_pass_bound p m Hwf Hm) as Hpass.
      change (T_narrow_step p m <= c_pass * pass_work p)%N in Hpass.
      time_unfold @T_loop_fuel; unfold narrow_step at 1.
      destruct (C.check p (narrow_candidate p m)) eqn:Hcheck; time_cbn.
      + specialize (IH (narrow_candidate p m) Hwf (narrow_candidate_inv p m Hwf Hm)).
        clear -Hpass IH; nia.
      + clear -Hpass; nia.
  Qed.

  (** Every refinement pass fits the same invariant budget. *)
  Lemma T_refine_le : forall p k m, S.wf p ->
    (forall x, B.inv p (C.look m x)) ->
    (T_refine p k m <= c_nar * N.of_nat (k + 1) * pass_work p)%N.
  Proof.
    intros p k m Hwf Hm.
    pose proof (T_refine_loop_le p k m Hwf Hm) as Hloop.
    pose proof (pass_work_pos p) as Hpositive.
    assert (Hbudget : (2 <= c_pass * pass_work p)%N).
    { unfold c_pass, c_base; clear -Hpositive; nia. }
    unfold T_refine.
    change (fun st => T_narrow_step p st) with (T_narrow_step p).
    eapply N.le_trans with (m := (2 * (c_pass * pass_work p) * (N.of_nat k + 1))%N).
    - clear -Hloop Hbudget; nia.
    - unfold c_nar, c_pass; rewrite Nat2N.inj_add; time_cbn.
      apply N.le_refl || (replace (N.of_nat 0) with 0%N by reflexivity; nia).
  Qed.

  (** One pass is linear in the sweep measure of the program. *)
  Lemma narrow_pass_complexity :
    T_narrow_pass p m ∈ 𝑂(pass_work p)
    for (p, m) | S.wf p /\ forall x, B.inv p (C.look m x).
  Proof.
    apply bigO_intro with (c := c_nar).
    intros [p m] [Hwf Hm]; cbn [fst snd] in *.
    pose proof (T_narrow_pass_le p m Hwf Hm) as Hpass; lia.
  Qed.

  (** Refinement is linear in the pass count times the sweep measure. *)
  Lemma refine_complexity :
    T_refine p k m ∈ 𝑂((N.of_nat (k + 1) * pass_work p)%N)
    for (p, k, m) | S.wf p /\ forall x, B.inv p (C.look m x).
  Proof.
    apply bigO_intro with (c := c_nar).
    intros [[p k] m] [Hwf Hm]; cbn [fst snd] in *.
    pose proof (T_refine_le p k m Hwf Hm) as Hrefine; nia.
  Qed.
End NarrowT.
