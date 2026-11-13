(** * Checked narrowing

    Each pass aggregates row contributions against a frozen store.
    For example, a rejected candidate leaves the input store unchanged.
    Builds on: Fixpoint.NarrowSig and Fixpoint.Query. *)

From Stdlib Require Import List Bool PeanoNat PArith NArith.
From Argent Require Import Time Tactics Std Loop.
From Galois.Base Require Import Code MapSig Trie.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig CheckSig NarrowSig.
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
  Definition refine p n m :=
    match loop_fuel (fun st => @inl (kmap S.key L.t) unit (narrow_pass p st)) n m with
    | inl result => result
    | inr _ => m
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

  (** Refinement performs exactly the requested number of checked passes. *)
  Lemma refine_spec : forall p n m, refine p n m = Nat.iter n (narrow_pass p) m.
  Proof.
    intros p n m; unfold refine; now rewrite refine_loop_spec.
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
  TimeFun refine.

  Definition c_nar : N := 1%N. (* STUB *)
  Definition pass_work (p : S.prog) : N :=
    (N.of_nat ((fold_right Nat.add 0
      (List.map (fun r => length (S.deps p r) + length (S.sides p r) + 1) (S.rows p)) + 1)%nat) *
    (S.row_work p (B.vsize p) + N.of_nat (S.kw p) +
      L.c_lat * N.of_nat (B.vsize p + 1) + 1))%N.
  (** One pass fits a budgeted row sweep. *)
  Lemma T_narrow_pass_le : forall p m, S.wf p ->
    (forall x, B.inv p (C.look m x)) -> (T_narrow_pass p m <= c_nar * pass_work p)%N.
  Proof. Admitted. (* STUB *)
  (** Every refinement pass fits the same invariant budget. *)
  Lemma T_refine_le : forall p k m, S.wf p ->
    (forall x, B.inv p (C.look m x)) ->
    (T_refine p k m <= c_nar * N.of_nat (k + 1) * pass_work p)%N.
  Proof. Admitted. (* STUB *)
End NarrowT.
