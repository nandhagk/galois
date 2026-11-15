(** * Checked sequentialisation of parallel moves

    An indexed depth-first producer breaks cycles with a temporary. Its independent checker
    compares the original source of every affected variable after symbolic execution.
    For example, a swap saves one source before either parallel destination is overwritten.
    Builds on: ParMoveSig and the canonical binary trie. *)

From Stdlib Require Import List PArith NArith Bool Lia.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import Trie.
From Galois.Ssa Require Import ParMoveSig.

Import List.ListNotations.

Module ListDef.
  TimeFun List.firstn.
End ListDef.

(** Missing bindings represent variables that still contain their own initial value. *)
Definition move_lookup (table : ptrie positive) (x : positive) : positive :=
  match trie_get x table with Some y => y | None => x end.
TimeFun move_lookup.

Fixpoint symbolic_run (sq : moves) (table : ptrie positive) : ptrie positive :=
  match sq with
  | [] => table
  | (dst, src) :: rest =>
    symbolic_run rest (PTrieCode.set dst (move_lookup table src) table)
  end.
TimeFun symbolic_run.

(** Right-to-left insertion retains the first parallel destination when a key repeats. *)
Fixpoint parallel_table (par : moves) : ptrie positive :=
  match par with
  | [] => Empty
  | (dst, src) :: rest => PTrieCode.set dst src (parallel_table rest)
  end.
TimeFun parallel_table.

Definition move_agrees (parallel sequential : ptrie positive) (tmp x : positive) : bool :=
  Pos.eqb x tmp || Pos.eqb (move_lookup sequential x) (move_lookup parallel x).
TimeFun move_agrees.

Fixpoint check_destinations (parallel sequential : ptrie positive) (tmp : positive)
    (ms : moves) : bool :=
  match ms with
  | [] => true
  | (dst, _) :: rest =>
    move_agrees parallel sequential tmp dst && check_destinations parallel sequential tmp rest
  end.
TimeFun check_destinations.

Inductive move_job : Type :=
  | MoveEnter (m : positive * positive)
  | MoveScan (ms : moves)
  | MoveFinish (m : positive * positive).

Record move_state : Type := MoveState {
  move_jobs : list move_job;
  move_seen : ptrie bool;
  move_redirect : ptrie unit;
  move_output : moves;
  move_cycles : list positive
}.
TimeFun move_jobs.
TimeFun move_seen.
TimeFun move_redirect.
TimeFun move_output.
TimeFun move_cycles.

Fixpoint incoming_moves (par : moves) (table : ptrie moves) : ptrie moves :=
  match par with
  | [] => table
  | (dst, src) :: rest =>
    let previous := match trie_get src table with Some ms => ms | None => [] end in
    incoming_moves rest (PTrieCode.set src ((dst, src) :: previous) table)
  end.
TimeFun incoming_moves.

Definition incoming_at (table : ptrie moves) (x : positive) : moves :=
  match trie_get x table with Some ms => ms | None => [] end.
TimeFun incoming_at.

(** Each loop step inspects one job; scans place one child at a time on the stack. *)
Definition move_step (incoming : ptrie moves) (tmp : positive) (st : move_state) : move_state :=
  match move_jobs st with
  | [] => st
  | job :: jobs =>
    match job with
    | MoveScan [] =>
      MoveState jobs (move_seen st) (move_redirect st) (move_output st) (move_cycles st)
    | MoveScan (m :: ms) =>
      MoveState (MoveEnter m :: MoveScan ms :: jobs)
        (move_seen st) (move_redirect st) (move_output st) (move_cycles st)
    | MoveEnter (dst, src) =>
      match trie_get dst (move_seen st) with
      | None =>
        MoveState (MoveScan (incoming_at incoming dst) :: MoveFinish (dst, src) :: jobs)
          (PTrieCode.set dst false (move_seen st)) (move_redirect st)
          (move_output st) (move_cycles st)
      | Some true =>
        MoveState jobs (move_seen st) (move_redirect st) (move_output st) (move_cycles st)
      | Some false =>
        match trie_get dst (move_redirect st) with
        | Some _ =>
          MoveState jobs (move_seen st) (move_redirect st) (move_output st) (move_cycles st)
        | None =>
          MoveState jobs (move_seen st) (PTrieCode.set dst tt (move_redirect st))
            ((tmp, src) :: move_output st) (dst :: move_cycles st)
        end
      end
    | MoveFinish (dst, src) =>
      let source := match trie_get dst (move_redirect st) with Some _ => tmp | None => src end in
      MoveState jobs (PTrieCode.set dst true (move_seen st)) (move_redirect st)
        ((dst, source) :: move_output st) (move_cycles st)
    end
  end.
TimeFun move_step.

Fixpoint move_run (fuel : nat) (incoming : ptrie moves) (tmp : positive)
    (st : move_state) : move_state :=
  match fuel with
  | O => st
  | S rest =>
    match move_jobs st with
    | [] => st
    | _ :: _ => move_run rest incoming tmp (move_step incoming tmp st)
    end
  end.
TimeFun move_run.

Definition move_initial (par : moves) : move_state :=
  MoveState [MoveScan par] Empty Empty [] [].
TimeFun move_initial.

Definition move_resolve (par : moves) (tmp : positive) : move_state :=
  move_run (8 * length par + 4) (incoming_moves par Empty) tmp (move_initial par).
TimeFun move_resolve.

Module ParMoveCode <: PARMOVE_OPS.
  (** The cap also bounds results for malformed inputs with repeated destinations. *)
  Definition seq (par : moves) (tmp : positive) : moves :=
    firstn (2 * length par) (rev_append (move_output (move_resolve par tmp)) []).

  Definition symbolic_all (sq : moves) : ptrie positive := symbolic_run sq Empty.
  Definition symbolic (sq : moves) (x : positive) : option positive :=
    Some (move_lookup (symbolic_all sq) x).

  Definition check_moves (par : moves) (tmp : positive) (sq : moves) : bool :=
    let parallel := parallel_table par in
    let sequential := symbolic_all sq in
    check_destinations parallel sequential tmp par &&
      check_destinations parallel sequential tmp sq.
End ParMoveCode.
(** Table lookup reflects the most recent symbolic assignment. *)
Lemma move_lookup_set table dst src x :
  move_lookup (PTrieCode.set dst src table) x =
    if Pos.eqb x dst then src else move_lookup table x.
Proof.
  unfold move_lookup. destruct (Pos.eqb x dst) eqn:Hequal.
  - apply Pos.eqb_eq in Hequal. subst x. rewrite PTrie.get_set_same. reflexivity.
  - apply Pos.eqb_neq in Hequal. rewrite PTrie.get_set_other by exact Hequal.
    reflexivity.
Qed.

(** An empty table leaves every variable at its original name. *)
Lemma move_lookup_empty x : move_lookup Empty x = x.
Proof.
  unfold move_lookup. rewrite PTrie.get_empty. reflexivity.
Qed.

(** Sequential execution depends only on pointwise values of the starting environment. *)
Lemma exec_seq_ext {A} (sq : moves) : forall (env other : positive -> option A) x,
  (forall y, env y = other y) -> exec_seq sq env x = exec_seq sq other x.
Proof.
  induction sq as [|[dst src] rest IH]; intros env other x Hagree; cbn [exec_seq].
  - apply Hagree.
  - apply IH. intro y. destruct (Pos.eqb y dst); apply Hagree.
Qed.

(** The symbolic table tracks execution from any starting symbolic table. *)
Lemma symbolic_run_correct (sq : moves) : forall table x,
  exec_seq sq (fun y => Some (move_lookup table y)) x =
    Some (move_lookup (symbolic_run sq table) x).
Proof.
  induction sq as [|[dst src] rest IH]; intros table x; cbn [exec_seq symbolic_run].
  - reflexivity.
  - transitivity (exec_seq rest
      (fun y => Some (move_lookup (PTrieCode.set dst (move_lookup table src) table) y)) x).
    + apply exec_seq_ext. intro y. rewrite move_lookup_set.
      destruct (Pos.eqb y dst); reflexivity.
    + apply IH.
Qed.

(** Parallel indexing preserves the public first-destination-wins semantics. *)
Lemma parallel_table_correct (par : moves) : forall x,
  Some (move_lookup (parallel_table par) x) = exec_par par (@Some positive) x.
Proof.
  induction par as [|[dst src] rest IH]; intro x; cbn [parallel_table exec_par].
  - rewrite move_lookup_empty. reflexivity.
  - rewrite move_lookup_set. destruct (Pos.eqb x dst); [reflexivity|apply IH].
Qed.

(** Acceptance equates the two tables on every checked non-temporary destination. *)
Lemma check_destinations_sound parallel sequential tmp ms :
  check_destinations parallel sequential tmp ms = true ->
  forall x, In x (map fst ms) -> x <> tmp ->
    move_lookup sequential x = move_lookup parallel x.
Proof.
  induction ms as [|[dst src] rest IH]; cbn [check_destinations map fst].
  - intros _ x Hin. contradiction.
  - rewrite Bool.andb_true_iff. intros [Hhead Htail] x [Hequal|Hin] Htmp.
    + subst x. unfold move_agrees in Hhead. apply Bool.orb_true_iff in Hhead.
      destruct Hhead as [Htmp'|Hagree].
      * apply Pos.eqb_eq in Htmp'. contradiction.
      * now apply Pos.eqb_eq.
    + exact (IH Htail x Hin Htmp).
Qed.

(** A variable not written by a sequential move list keeps its starting value. *)
Lemma exec_seq_unwritten {A} (sq : moves) : forall (env : positive -> option A) x,
  ~ In x (map fst sq) -> exec_seq sq env x = env x.
Proof.
  induction sq as [|[dst src] rest IH]; intros env x Houtside; cbn [exec_seq].
  - reflexivity.
  - rewrite IH by (intro Hin; apply Houtside; now right).
    destruct (Pos.eqb x dst) eqn:Hequal; [|reflexivity].
    apply Pos.eqb_eq in Hequal. subst x. exfalso. apply Houtside. now left.
Qed.

(** A variable not written by a parallel move list keeps its starting value. *)
Lemma exec_par_unwritten {A} (par : moves) : forall (env : positive -> option A) x,
  ~ In x (map fst par) -> exec_par par env x = env x.
Proof.
  induction par as [|[dst src] rest IH]; intros env x Houtside; cbn [exec_par].
  - reflexivity.
  - destruct (Pos.eqb x dst) eqn:Hequal.
    + apply Pos.eqb_eq in Hequal. subst x. exfalso. apply Houtside. now left.
    + apply IH. intro Hin. apply Houtside. now right.
Qed.

(** Relabelling values commutes with sequential assignment. *)
Lemma exec_seq_map {A B} (sq : moves) : forall (env : positive -> option A)
    (f : option A -> option B) x,
  exec_seq sq (fun y => f (env y)) x = f (exec_seq sq env x).
Proof.
  induction sq as [|[dst src] rest IH]; intros env f x; cbn [exec_seq].
  - reflexivity.
  - transitivity (exec_seq rest
      (fun y => f (if Pos.eqb y dst then env src else env y)) x).
    + apply exec_seq_ext. intro y. destruct (Pos.eqb y dst); reflexivity.
    + apply IH.
Qed.

(** Relabelling values commutes with parallel assignment. *)
Lemma exec_par_map {A B} (par : moves) : forall (env : positive -> option A)
    (f : option A -> option B) x,
  exec_par par (fun y => f (env y)) x = f (exec_par par env x).
Proof.
  induction par as [|[dst src] rest IH]; intros env f x; cbn [exec_par].
  - reflexivity.
  - destruct (Pos.eqb x dst); [reflexivity|apply IH].
Qed.

(** Symbolic names carry all information needed for execution in an arbitrary environment. *)
Lemma symbolic_transport par sq x :
  exec_seq sq (@Some positive) x = exec_par par (@Some positive) x ->
  forall A (env : positive -> option A), exec_seq sq env x = exec_par par env x.
Proof.
  intros Hagree A env.
  pose proof (@exec_seq_map positive A sq (@Some positive)
    (fun o => match o with Some z => env z | None => None end) x) as Hseq.
  pose proof (@exec_par_map positive A par (@Some positive)
    (fun o => match o with Some z => env z | None => None end) x) as Hpar.
  change (exec_seq sq env x =
    match exec_seq sq (@Some positive) x with Some z => env z | None => None end) in Hseq.
  change (exec_par par env x =
    match exec_par par (@Some positive) x with Some z => env z | None => None end) in Hpar.
  rewrite Hseq, Hpar, Hagree. reflexivity.
Qed.


(** Every indexed predecessor remains one of the input move occurrences. *)
Definition incoming_known (par : moves) (table : ptrie moves) : Prop :=
  forall x m, In m (incoming_at table x) -> In m par.

Lemma incoming_at_empty x : incoming_at Empty x = [].
Proof.
  unfold incoming_at. rewrite PTrie.get_empty. reflexivity.
Qed.

Lemma incoming_moves_known par rest : forall table,
  incl rest par -> incoming_known par table -> incoming_known par (incoming_moves rest table).
Proof.
  induction rest as [|[dst src] rest IH]; intros table Hrest Htable; cbn [incoming_moves].
  - exact Htable.
  - apply IH.
    + intros m Hin. apply Hrest. now right.
    + intros x m Hin. unfold incoming_at in Hin.
      destruct (Pos.eq_dec x src) as [Hequal|Hdifferent].
      * subst x. rewrite PTrie.get_set_same in Hin. cbn in Hin.
        destruct Hin as [Hequal|Hin].
        -- subst m. apply Hrest. now left.
        -- apply (Htable src m). exact Hin.
      * rewrite PTrie.get_set_other in Hin by exact Hdifferent.
        exact (Htable x m Hin).
Qed.

(** A pending job contains only moves from the original parallel assignment. *)
Definition job_known (par : moves) (job : move_job) : Prop :=
  match job with
  | MoveEnter m | MoveFinish m => In m par
  | MoveScan ms => Forall (fun m => In m par) ms
  end.

Definition move_allowed (par : moves) (tmp : positive) (m : positive * positive) : Prop :=
  (In (fst m) (map fst par) \/ fst m = tmp) /\
  (In (snd m) (map snd par) \/ snd m = tmp).

Definition move_known (par : moves) (tmp : positive) (st : move_state) : Prop :=
  Forall (job_known par) (move_jobs st) /\ Forall (move_allowed par tmp) (move_output st).

Lemma move_allowed_original par tmp dst src :
  In (dst, src) par -> move_allowed par tmp (dst, src).
Proof.
  intro Hin. split; left; [exact (in_map fst par (dst, src) Hin)|
    exact (in_map snd par (dst, src) Hin)].
Qed.

Lemma move_allowed_save par tmp dst src :
  In (dst, src) par -> move_allowed par tmp (tmp, src).
Proof.
  intro Hin. split; [now right|left]. exact (in_map snd par (dst, src) Hin).
Qed.

Lemma move_allowed_restore par tmp dst src :
  In (dst, src) par -> move_allowed par tmp (dst, tmp).
Proof.
  intro Hin. split; [left|now right]. exact (in_map fst par (dst, src) Hin).
Qed.

(** DFS jobs and emitted operands preserve their input provenance. *)
Lemma move_step_known par incoming tmp st :
  incoming_known par incoming -> move_known par tmp st ->
  move_known par tmp (move_step incoming tmp st).
Proof.
  intros Hinput [Hjobs Houtput]. destruct st as [jobs seen redirect output cycles].
  destruct jobs as [|job jobs]; [now split|].
  cbn [move_jobs move_output] in Hjobs, Houtput.
  inversion Hjobs as [|head tail Hjob Htail]; subst head tail.
  destruct job as [[dst src]|ms|[dst src]]; cbn [job_known] in Hjob.
  - cbn [move_step move_jobs move_seen move_redirect move_output move_cycles].
    destruct (trie_get dst seen) as [[|]|] eqn:Hseen.
    + now split.
    + destruct (trie_get dst redirect) as [u|] eqn:Hredirect; [now split|].
      split; [exact Htail|]. constructor; [now apply move_allowed_save with dst|exact Houtput].
    + split; [|exact Houtput]. constructor.
      * apply Forall_forall. intros m Hin. exact (Hinput dst m Hin).
      * constructor; assumption.
  - destruct ms as [|m ms]; cbn [move_step move_jobs move_seen move_redirect
      move_output move_cycles].
    + now split.
    + inversion Hjob as [|first tail Hfirst Hrest]; subst first tail.
      split; [repeat constructor; assumption|exact Houtput].
  - cbn [move_step move_jobs move_seen move_redirect move_output move_cycles].
    split; [exact Htail|]. constructor; [|exact Houtput].
    destruct (trie_get dst redirect) as [u|]; [now apply move_allowed_restore with src|
      now apply move_allowed_original].
Qed.

Lemma move_run_known fuel par incoming tmp : forall st,
  incoming_known par incoming -> move_known par tmp st ->
  move_known par tmp (move_run fuel incoming tmp st).
Proof.
  induction fuel as [|fuel IH]; intros st Hinput Hstate; cbn [move_run]; [exact Hstate|].
  destruct (move_jobs st); [exact Hstate|]. apply IH; [exact Hinput|].
  now apply move_step_known.
Qed.

Lemma move_resolve_known par tmp : move_known par tmp (move_resolve par tmp).
Proof.
  unfold move_resolve. apply move_run_known.
  - apply incoming_moves_known; [apply incl_refl|]. intros x m Hin.
    rewrite incoming_at_empty in Hin. contradiction.
  - split; [|constructor]. constructor; [|constructor].
    apply Forall_forall. intros m Hin. exact Hin.
Qed.


(** Every recorded cycle destination has a unique redirection marker. *)
Definition cycles_known (par : moves) (st : move_state) : Prop :=
  NoDup (move_cycles st) /\ incl (move_cycles st) (map fst par) /\
  forall x, In x (move_cycles st) -> trie_get x (move_redirect st) = Some tt.

Lemma cycles_add_known par jobs seen redirect output cycles dst src :
  In (dst, src) par -> trie_get dst redirect = None ->
  cycles_known par (MoveState jobs seen redirect output cycles) ->
  forall jobs' seen' output',
  cycles_known par (MoveState jobs' seen' (PTrieCode.set dst tt redirect) output'
    (dst :: cycles)).
Proof.
  intros Hin Hfresh [Hdistinct [Hmembers Hmarked]] jobs' seen' output'.
  unfold cycles_known. cbn [move_cycles move_redirect] in *. split.
  - constructor; [|exact Hdistinct]. intro Hcycle.
    specialize (Hmarked dst Hcycle). rewrite Hfresh in Hmarked. discriminate.
  - split.
    + intros x [Hequal|Hcycle].
      * subst x. exact (in_map fst par (dst, src) Hin).
      * exact (Hmembers x Hcycle).
    + intros x [Hequal|Hcycle].
      * subst x. apply PTrie.get_set_same.
      * destruct (Pos.eq_dec x dst) as [Hequal|Hdifferent].
        -- subst x. apply PTrie.get_set_same.
        -- rewrite PTrie.get_set_other by exact Hdifferent. exact (Hmarked x Hcycle).
Qed.

Lemma move_step_cycles_known par incoming tmp st :
  Forall (job_known par) (move_jobs st) -> cycles_known par st ->
  cycles_known par (move_step incoming tmp st).
Proof.
  intros Hjobs Hcycles. destruct st as [jobs seen redirect output cycles].
  destruct jobs as [|job jobs]; [exact Hcycles|].
  cbn [move_jobs] in Hjobs. inversion Hjobs as [|head tail Hjob Htail]; subst head tail.
  destruct job as [[dst src]|ms|[dst src]]; cbn [job_known] in Hjob.
  - cbn [move_step move_jobs move_seen move_redirect move_output move_cycles].
    destruct (trie_get dst seen) as [[|]|]; [exact Hcycles| |exact Hcycles].
    destruct (trie_get dst redirect) as [u|] eqn:Hredirect; [exact Hcycles|].
    exact (cycles_add_known par _ _ _ _ _ dst src Hjob Hredirect Hcycles _ _ _).
  - destruct ms; exact Hcycles.
  - cbn [move_step move_jobs move_seen move_redirect move_output move_cycles].
    exact Hcycles.
Qed.

Lemma move_run_cycles_known fuel par incoming tmp : forall st,
  incoming_known par incoming -> move_known par tmp st -> cycles_known par st ->
  cycles_known par (move_run fuel incoming tmp st).
Proof.
  induction fuel as [|fuel IH]; intros st Hinput Hstate Hcycles; cbn [move_run].
  - exact Hcycles.
  - destruct (move_jobs st); [exact Hcycles|]. apply IH; [exact Hinput| |].
    + now apply move_step_known.
    + apply move_step_cycles_known; [exact (proj1 Hstate)|exact Hcycles].
Qed.

Lemma move_resolve_cycles_known par tmp : cycles_known par (move_resolve par tmp).
Proof.
  unfold move_resolve. apply move_run_cycles_known.
  - apply incoming_moves_known; [apply incl_refl|]. intros x m Hin.
    rewrite incoming_at_empty in Hin. contradiction.
  - split; [|constructor]. constructor; [|constructor].
    apply Forall_forall. intros m Hin. exact Hin.
  - split; [constructor|]. split; intros x Hin; contradiction.
Qed.


Module ParMove <: PARMOVE.
  Include ParMoveCode.

  (** The public symbolic table agrees with execution from distinct variable names. *)
  Lemma symbolic_all_correct sq x :
    exec_seq sq (@Some positive) x = Some (move_lookup (symbolic_all sq) x).
  Proof.
    unfold symbolic_all. rewrite <- symbolic_run_correct.
    apply exec_seq_ext. intro y. rewrite move_lookup_empty. reflexivity.
  Qed.

  (** Checking all written destinations suffices for global symbolic agreement. *)
  Lemma check_moves_symbolic par tmp sq : check_moves par tmp sq = true ->
    forall x, x <> tmp -> exec_seq sq (@Some positive) x = exec_par par (@Some positive) x.
  Proof.
    unfold check_moves. rewrite Bool.andb_true_iff. intros [Hpar Hseq] x Htmp.
    destruct (in_dec Pos.eq_dec x (map fst par)) as [Hin|Houtside].
    - rewrite symbolic_all_correct, <- parallel_table_correct.
      f_equal. exact (check_destinations_sound _ _ _ _ Hpar x Hin Htmp).
    - destruct (in_dec Pos.eq_dec x (map fst sq)) as [Hin|Houtside_seq].
      + rewrite symbolic_all_correct, <- parallel_table_correct.
        f_equal. exact (check_destinations_sound _ _ _ _ Hseq x Hin Htmp).
      + rewrite exec_seq_unwritten by exact Houtside_seq.
        rewrite exec_par_unwritten by exact Houtside. reflexivity.
  Qed.


  Lemma check_moves_sound : forall par tmp sq,
    NoDup (map fst par) -> ~ In tmp (map fst par ++ map snd par) ->
    check_moves par tmp sq = true -> forall A (env : positive -> option A) x,
      x <> tmp -> exec_seq sq env x = exec_par par env x.
  Proof.
    intros par tmp sq _ _ Hcheck A env x Htmp.
    apply symbolic_transport. exact (check_moves_symbolic par tmp sq Hcheck x Htmp).
  Qed.
  Lemma seq_length : forall par tmp, length (seq par tmp) <= 2 * length par.
  Proof.
    intros par tmp. unfold seq. rewrite length_firstn. lia.
  Qed.
  Lemma seq_ids : forall par tmp m, In m (seq par tmp) ->
    (In (fst m) (map fst par) \/ fst m = tmp) /\
    (In (snd m) (map snd par) \/ snd m = tmp).
  Proof.
    intros par tmp m Hin. unfold seq in Hin.
    pose proof (proj2 (move_resolve_known par tmp)) as Houtput.
    rewrite rev_append_rev, app_nil_r in Hin.
    assert (Hfull : In m (rev (move_output (move_resolve par tmp)))).
    { rewrite <- (firstn_skipn (2 * length par) (rev (move_output (move_resolve par tmp)))).
      apply in_or_app. now left. }
    apply (proj2 (in_rev _ _)) in Hfull.
    now apply (proj1 (Forall_forall _ _) Houtput m Hfull).
  Qed.
End ParMove.

Module ParMoveT <: PARMOVE_ALL.
  Include ParMove.
  TimeFun seq.
  TimeFun symbolic_all.
  TimeFun check_moves.
  Definition c_pm : N := 1. (* STUB *)
  Lemma T_seq_le : forall par tmp,
    (T_seq par tmp <= c_pm * N.of_nat (length par + 1) * N.of_nat (bits_of par + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_check_moves_le : forall par tmp sq,
    (T_check_moves par tmp sq <= c_pm * N.of_nat (length par + length sq + 1) *
      N.of_nat (bits_of (par ++ sq) + 1))%N.
  Proof. Admitted. (* STUB *)

  TimeFun symbolic.
  Definition cycle_search (par : moves) : list positive :=
    move_cycles (move_resolve par 1%positive).
  TimeFun cycle_search.
  Definition k_symbolic : N := 1. (* STUB *)
  Definition k_cycle : N := 1. (* STUB *)
  Lemma F0_cycle_search : forall par,
    NoDup (cycle_search par) /\ forall x, In x (cycle_search par) -> In x (map fst par).
  Proof.
    intro par. pose proof (move_resolve_cycles_known par 1%positive) as Hcycles.
    exact (conj (proj1 Hcycles) (proj1 (proj2 Hcycles))).
  Qed.
  Lemma T0_cycle_search : forall par,
    (T_cycle_search par <= k_cycle * N.of_nat (length par + 1) *
      N.of_nat (bits_of par + 1))%N.
  Proof. Admitted. (* STUB *)
  Definition relevant (par sq : moves) := map fst par ++ map snd par ++ map fst sq ++ map snd sq.
  Lemma F1_symbolic_all : forall sq x,
    exec_seq sq (@Some positive) x =
      match trie_get x (symbolic_all sq) with Some y => Some y | None => Some x end.
  Proof.
    intros sq x. rewrite symbolic_all_correct. unfold move_lookup.
    destruct (trie_get x (symbolic_all sq)); reflexivity.
  Qed.
  Lemma F1_symbolic : forall sq x, symbolic sq x = exec_seq sq (@Some positive) x.
  Proof.
    intros sq x. symmetry. apply symbolic_all_correct.
  Qed.
  Lemma F2_check_symbolic : forall par tmp sq, check_moves par tmp sq = true ->
    forall x, In x (relevant par sq) -> x <> tmp ->
      symbolic sq x = exec_par par (@Some positive) x.
  Proof.
    intros par tmp sq Hcheck x _ Htmp. rewrite F1_symbolic.
    exact (check_moves_symbolic par tmp sq Hcheck x Htmp).
  Qed.
  Lemma F3_unaffected : forall par sq x, ~ In x (relevant par sq) ->
    exec_seq sq (@Some positive) x = Some x /\ exec_par par (@Some positive) x = Some x.
  Proof.
    intros par sq x Houtside. split.
    - apply exec_seq_unwritten. intro Hin. apply Houtside.
      unfold relevant. apply in_or_app. right. apply in_or_app. right.
      apply in_or_app. now left.
    - apply exec_par_unwritten. intro Hin. apply Houtside.
      unfold relevant. apply in_or_app. now left.
  Qed.
  Lemma F4_symbolic_transport : forall par sq x,
    exec_seq sq (@Some positive) x = exec_par par (@Some positive) x ->
    forall A (env : positive -> option A), exec_seq sq env x = exec_par par env x.
  Proof.
    exact symbolic_transport.
  Qed.
  Lemma T1_symbolic_all : forall sq,
    (T_symbolic_all sq <= k_symbolic * N.of_nat (length sq + 1) *
      N.of_nat (bits_of sq + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T1_seq : forall par tmp,
    (T_seq par tmp <= T_cycle_search par + k_cycle *
      N.of_nat (length par + 1) * N.of_nat (bits_of par + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T2_check : forall par tmp sq,
    (T_check_moves par tmp sq <= T_symbolic_all sq + k_symbolic * N.of_nat (length par + length sq + 1) *
      N.of_nat (bits_of (par ++ sq) + 1))%N.
  Proof. Admitted. (* STUB *)
End ParMoveT.
