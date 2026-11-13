(** * Least candidates from the concrete worklist solver

    A widening-free run retains values below every post-solution of its monotone system.
    For example, arbitrary priorities can change visit order without changing this bound.
    Builds on: WorklistCode, SolverSig, PolicySig, LatticeSig, Trie and Argent.Loop. *)

From Stdlib Require Import List Bool PArith NArith.
From Argent Require Import Loop.
From Galois.Base Require Import MapSig Trie HeapSig Loop.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig PolicySig SolverSig WorklistSig Worklist.

Import List.ListNotations.

(** Accessibility iteration transports a state invariant to its stopping result. *)
Lemma worklist_loop_preserves {A R : Type} (lt : A -> A -> Prop)
    (step : forall s, {s1 : A | lt s1 s} + R) (Inv : A -> Prop) (Post : R -> Prop) :
  (forall s, Inv s ->
    match step s with inl (exist _ s1 _) => Inv s1 | inr r => Post r end) ->
  forall s (H : Acc lt s), Inv s -> Post (loop lt step s H).
Proof.
  intros Hstep s H; induction H as [s Hnext IH] using Acc_ind_dep; intro Hinv.
  cbn [loop Acc_inv]; destruct (step s) as [[s1 Hlt]|r] eqn:Hcall.
  - apply IH; specialize (Hstep s Hinv); rewrite Hcall in Hstep; exact Hstep.
  - specialize (Hstep s Hinv); rewrite Hcall in Hstep; exact Hstep.
Qed.

(** Binary-fuel iteration preserves invariants on exhaustion and on normal return. *)
Lemma worklist_loopN_preserves {A R : Type} (step : A -> A + R)
    (Inv : A -> Prop) (Post : R -> Prop) :
  (forall s, Inv s -> match step s with inl s1 => Inv s1 | inr r => Post r end) ->
  forall fuel s, Inv s ->
    match loopN step fuel s with inl s1 => Inv s1 | inr r => Post r end.
Proof.
  intros Hstep fuel s Hinv; unfold loopN.
  apply (worklist_loop_preserves loopN_lt (loopN_step step)
    (fun fs => Inv (snd fs))
    (fun result => match result with inl s1 => Inv s1 | inr r => Post r end)).
  - intros [remaining current] Hcurrent; destruct remaining as [|p].
    + exact Hcurrent.
    + cbn [loopN_step]; specialize (Hstep current Hcurrent).
      destruct (step current) as [next|r] eqn:Hcall; exact Hstep.
  - exact Hinv.
Qed.

Module WorklistLeast (L : WLATTICE) (LB : LUB L) (S : SYSTEM L)
    (P : POLICY L) (Q : PQ_OPS).
  Module V := WorklistCode L S P Q.

  Definition no_heads (pol : policy L.wparam) : Prop :=
    forall c, trie_get c (heads pol) = None.

  Definition store_below (u : S.key -> L.t) (m : kmap S.key L.t) : Prop :=
    forall x, L.leb (look_or S.key_code L.bot m x) (u x) = true.

  Definition rows_listed (p : S.prog) (rows : ptrie S.row) : Prop :=
    forall id r, trie_get id rows = Some r -> In r (S.rows p).

  (** The row table only supplies listed rows, and every current value has the desired bound. *)
  Definition state_below (p : S.prog) (u : S.key -> L.t) (s : V.state) : Prop :=
    rows_listed p (ws_rows s) /\ store_below u (ws_store s).

  Definition result_below (u : S.key -> L.t) (result : outcome (kmap S.key L.t)) : Prop :=
    match result with
    | Solved m | OutOfFuel m => store_below u m
    | Rejected _ => True
    end.

  (** Enqueue changes queue metadata without changing stored values. *)
  Lemma enqueue_store : forall p pol ids s,
    ws_store (V.enqueue p pol ids s) = ws_store s.
  Proof.
    reflexivity.
  Qed.

  (** Enqueue retains the row table independently of queue validity. *)
  Lemma enqueue_rows : forall p pol ids s,
    ws_rows (V.enqueue p pol ids s) = ws_rows s.
  Proof.
    reflexivity.
  Qed.

  (** Each indexed row comes from an input occurrence of the indexing fold. *)
  Lemma index_rows_listed : forall p entries,
    (forall id r, In (id, r) entries -> In r (S.rows p)) ->
    rows_listed p (fst (fold_right (V.index_row p) (Empty, Empty) entries)).
  Proof.
    intros p entries; induction entries as [|[id r] rest IH]; intro Hentries.
    - intros q row Hget; cbn [fold_right fst] in Hget.
      rewrite PTrie.get_empty in Hget; discriminate Hget.
    - intros q row Hget; cbn [fold_right V.index_row fst snd] in Hget.
      destruct (Pos.eq_dec q id) as [->|Hneq].
      + rewrite PTrie.get_set_same in Hget; injection Hget as <-.
        apply (Hentries id r); now left.
      + rewrite PTrie.get_set_other in Hget by exact Hneq.
        apply (IH (fun j a Hin => Hentries j a (or_intror Hin)) q row Hget).
  Qed.

  (** Preparation starts at bottom with rows taken from the declared program list. *)
  Lemma prepare_below : forall p pol u, state_below p u (V.prepare p pol).
  Proof.
    intros p pol u; split; unfold V.prepare.
    - rewrite enqueue_rows; cbn [ws_rows]; apply index_rows_listed.
      intros id r Hin; eapply in_combine_r; exact Hin.
    - rewrite enqueue_store; cbn [ws_store]; intro x.
      unfold look_or; rewrite PTrie.get_empty; apply L.bot_least.
  Qed.

  (** Updating a value cannot replace any row-table entry. *)
  Lemma update_rows : forall p pol s xa,
    ws_rows (V.update_one p pol s xa) = ws_rows s.
  Proof.
    intros p pol s [x a]; unfold V.update_one.
    destruct (L.leb a (look_or S.key_code L.bot (ws_store s) x)); [reflexivity|].
    destruct (trie_get (S.key_code x) (ws_armed s)); cbn [V.arm ws_rows].
    - reflexivity.
    - rewrite enqueue_rows; reflexivity.
  Qed.

  (** Without heads, each strict update stores exactly the join with the old value. *)
  Lemma update_store : forall p pol s x a, no_heads pol ->
    ws_store (V.update_one p pol s (x, a)) =
    if L.leb a (look_or S.key_code L.bot (ws_store s) x) then ws_store s
    else PTrieCode.set (S.key_code x)
      (x, L.join (look_or S.key_code L.bot (ws_store s) x) a) (ws_store s).
  Proof.
    intros p pol s x a Hfree; unfold V.update_one.
    destruct (L.leb a (look_or S.key_code L.bot (ws_store s) x)) eqn:Hstable;
      [reflexivity|].
    rewrite P.update_spec, Hstable, Hfree; cbn [fst snd].
    destruct (trie_get (S.key_code x) (ws_armed s)); cbn [V.arm ws_store].
    - reflexivity.
    - rewrite enqueue_store; reflexivity.
  Qed.

  (** A bounded contribution joined into a bounded store remains bounded. *)
  Lemma update_below : forall p pol u s x a,
    no_heads pol -> store_below u (ws_store s) -> L.leb a (u x) = true ->
    store_below u (ws_store (V.update_one p pol s (x, a))).
  Proof.
    intros p pol u s x a Hfree Hstore Ha; rewrite update_store by exact Hfree.
    destruct (L.leb a (look_or S.key_code L.bot (ws_store s) x)); [exact Hstore|].
    intro y; destruct (S.key_eqb_spec y x) as [->|Hneq]; unfold look_or.
    - rewrite PTrie.get_set_same; apply LB.join_least; [apply Hstore|exact Ha].
    - rewrite PTrie.get_set_other; [apply Hstore|].
      intro Hcodes; apply Hneq, S.key_code_inj, Hcodes.
  Qed.

  (** Applying an ordered list of bounded contributions retains both invariant components. *)
  Lemma updates_below : forall p pol u outs,
    no_heads pol -> Forall (fun xa => L.leb (snd xa) (u (fst xa)) = true) outs ->
    forall s, state_below p u s ->
      state_below p u (fold_left (V.update_one p pol) outs s).
  Proof.
    intros p pol u outs Hfree Houts.
    induction Houts as [|[x a] rest Ha Hrest IH]; intros s [Hrows Hstore];
      cbn [fold_left].
    - split; assumption.
    - apply IH; split.
      + unfold rows_listed in *; rewrite update_rows; exact Hrows.
      + apply update_below; assumption.
  Qed.

  (** Pointwise side comparison transfers the post-solution bounds to the smaller side list. *)
  Lemma sides_below : forall (u : S.key -> L.t) (ss ts : list (S.key * L.t)),
    Forall2 (fun xa yb => fst xa = fst yb /\ L.leb (snd xa) (snd yb) = true) ss ts ->
    forallb (fun yb => L.leb (snd yb) (u (fst yb))) ts = true ->
    Forall (fun xa => L.leb (snd xa) (u (fst xa)) = true) ss.
  Proof.
    intros u ss ts Hrel; induction Hrel as [|[x a] [y b] ss ts Hhead Htail IH];
      intro Hbounds; cbn [forallb fst snd] in *.
    - constructor.
    - apply andb_true_iff in Hbounds as [Hb Hbounds].
      destruct Hhead as [Hkey Hab]; subst y; constructor.
      + eapply L.leb_trans; eassumption.
      + apply IH; exact Hbounds.
  Qed.

  (** A listed monotone row evaluated below a post-solution emits bounded contributions. *)
  Lemma outputs_below : forall p r u m a ss,
    S.monotone p -> In r (S.rows p) -> S.post_solution p u -> store_below u m ->
    V.eval_row p r m = Some (a, ss) ->
    Forall (fun xa => L.leb (snd xa) (u (fst xa)) = true) ((S.target p r, a) :: ss).
  Proof.
    intros p r u m a ss Hmono Hr Hpost Hstore Heval.
    change (S.eval p r (look_or S.key_code L.bot m) = Some (a, ss)) in Heval.
    specialize (Hmono r (look_or S.key_code L.bot m) u Hr Hstore).
    specialize (Hpost r Hr); rewrite Heval in Hmono.
    destruct (S.eval p r u) as [[b ts]|] eqn:Hout; cbn [out_leb] in Hmono;
      [|contradiction Hmono].
    destruct Hmono as [Hprimary Hsides]; cbn [row_ok] in Hpost.
    apply andb_true_iff in Hpost as [Htarget Hsides_bound]; constructor.
    - cbn [fst snd]; eapply L.leb_trans; eassumption.
    - eapply sides_below; eassumption.
  Qed.

  (** One callback preserves the store bound or returns a bounded candidate. *)
  Lemma step_below : forall p pol u,
    S.monotone p -> no_heads pol -> S.post_solution p u -> forall s,
    state_below p u s ->
    match V.step p pol s with
    | inl s1 => state_below p u s1
    | inr result => result_below u result
    end.
  Proof.
    intros p pol u Hmono Hfree Hpost s [Hrows Hstore]; unfold V.step.
    destruct (Q.pop (ws_queue s)) as [[[rank id] q]|]; [|exact Hstore].
    destruct (V.row_at s id) as [r|] eqn:Hrow; [|exact I].
    destruct (V.eval_row p r (ws_store s)) as [[a ss]|] eqn:Heval; [|exact I].
    apply updates_below; [exact Hfree| |].
    - eapply outputs_below; [exact Hmono| |exact Hpost|exact Hstore|exact Heval].
      apply (Hrows id r Hrow).
    - split; assumption.
  Qed.

  (** Every returned candidate, including an exhausted partial store, has the common bound. *)
  Lemma run_below : forall p pol fuel u,
    S.monotone p -> no_heads pol -> S.post_solution p u ->
    result_below u (V.run p pol fuel).
  Proof.
    intros p pol fuel u Hmono Hfree Hpost.
    pose proof (worklist_loopN_preserves (V.step p pol) (state_below p u) (result_below u)
      (step_below p pol u Hmono Hfree Hpost) fuel (V.prepare p pol)
      (prepare_below p pol u)) as Hloop.
    unfold V.run; destruct (loopN (V.step p pol) fuel (V.prepare p pol)) as [last|result].
    - exact (proj2 Hloop).
    - exact Hloop.
  Qed.

  Module Certificate <: SOLVER_LEAST L LB S V.
    Definition widening_free (pol : policy L.wparam) : Prop :=
      forall c, trie_get c (heads pol) = None.

    (** A solved widening-free candidate lies below every post-solution. *)
    Lemma run_least : forall p pol fuel m s', S.wf p -> S.monotone p ->
      widening_free pol -> V.run p pol fuel = Solved m -> S.post_solution p s' ->
      forall x, L.leb (look_or S.key_code L.bot m x) (s' x) = true.
    Proof.
      intros p pol fuel m s' Hwf Hmono Hfree Hrun Hpost.
      pose proof (run_below p pol fuel s' Hmono Hfree Hpost) as Hbelow.
      rewrite Hrun in Hbelow; exact Hbelow.
    Qed.
  End Certificate.
  Include Certificate.
End WorklistLeast.
