(** * Generic joins over tuple indexes

    Joins enumerate the assignments that satisfy every indexed projection.
    For example, a shared column binds the same cell in two relation indexes.
    Builds on: ValueSig, IndexSig and Syntax. *)

From Stdlib Require Import List PArith NArith Arith Sorting.Sorted.
From Argent Require Import Time Std.
From Galois.Egglog Require Import ValueSig IndexSig Syntax.

Import List.ListNotations.

Definition project_cells {V : Type} (lv : list nat) (b : list (cell V))
    : option (list (cell V)) :=
  fold_right (fun i acc =>
    match nth_error b i, acc with
    | Some c, Some cs => Some (c :: cs)
    | _, _ => None
    end) (Some []) lv.
TimeFun project_cells.

Module Type JOIN_OPS (V : VALUE_OPS) (I : INDEX_OPS V).
  Parameter run : jplan -> list I.t -> list (list (cell V.t)).
End JOIN_OPS.

Module Type JOIN_SPEC (V : VALUE) (I : INDEX V) (Import X : JOIN_OPS V I).
  Definition project := @project_cells V.t.
  Definition answer (p : jplan) (ixs : list I.t) (b : list (cell V.t)) : Prop :=
    length b = nvars p /\
    Forall2 (fun lv ix => exists u, project lv b = Some u /\ I.mem ix u) (cols p) ixs.
  Definition wf_plan (p : jplan) (ixs : list I.t) : Prop :=
    length (cols p) = length ixs /\
    Forall2 (fun lv ix => StronglySorted lt lv /\
      Forall (fun i => i < nvars p) lv /\ I.wf (length lv) ix) (cols p) ixs /\
    (forall i, i < nvars p -> exists lv, In lv (cols p) /\ In i lv).
End JOIN_SPEC.

Module Type JOIN_LAWS (V : VALUE) (I : INDEX V) (Import X : JOIN_OPS V I)
    (Import XS : JOIN_SPEC V I X).
  (** Every emitted assignment satisfies every input index. *)
  Parameter run_sound : forall p ixs b, wf_plan p ixs ->
    In b (run p ixs) -> answer p ixs b.
  (** Every satisfying assignment is emitted. *)
  Parameter run_complete : forall p ixs b, wf_plan p ixs ->
    answer p ixs b -> In b (run p ixs).
  (** Assignments are emitted once. *)
  Parameter run_nodup : forall p ixs, wf_plan p ixs -> NoDup (run p ixs).
End JOIN_LAWS.

Module Type JOIN (V : VALUE) (I : INDEX V) :=
  JOIN_OPS V I <+ JOIN_SPEC V I <+ JOIN_LAWS V I.

Module Type JOIN_TIME (V : VALUE_T) (I : INDEX_T V) (Import X : JOIN V I).
  (* spec: work wmax *)
  Parameter work wmax : jplan -> list I.t -> nat.
  Parameter T_run : jplan -> list I.t -> nat.
  Parameter c_join : nat.
  (** Running pays for recursive probe work at the maximum index width. *)
  (* SIG-QUESTION: For zero variables and arbitrarily many empty-column indexes,
     the requested recurrence gives work = 1 while root-node initialization visits
     every index. The public bound is retained for F1 without an added cost term. *)
  Parameter T_run_le : forall p ixs, wf_plan p ixs ->
    T_run p ixs <= c_join * (work p ixs + 1) * (wmax p ixs + 1).
  (** Recursive probe work is a lower bound on running time. *)
  Parameter T_run_ge : forall p ixs, wf_plan p ixs -> work p ixs <= T_run p ixs.
End JOIN_TIME.

Module Type JOIN_T (V : VALUE_T) (I : INDEX_T V) := JOIN V I <+ JOIN_TIME V I.

Module Type JOIN_PLAN (V : VALUE_T) (I : INDEX_T V) (Import X : JOIN_T V I).
  (** Current nodes represent the columns already bound by the reversed prefix. *)
  Definition nodes_ok (p : jplan) (ixs : list I.t) (lvl : nat)
      (pre : list (cell V.t)) (ns : list positive) : Prop :=
    wf_plan p ixs /\ length pre = lvl /\ lvl <= nvars p /\
    Forall2 (fun lvix n => exists u,
      project (filter (fun i => Nat.ltb i lvl) (fst lvix)) (rev pre) = Some u /\
      I.node (snd lvix) n u) (combine (cols p) ixs) ns.
  Parameter advance : jplan -> list I.t -> nat -> list positive -> cell V.t ->
    option (list positive).
  Parameter go : nat -> jplan -> list I.t -> list positive -> list (cell V.t) ->
    list (list (cell V.t)) -> list (list (cell V.t)).
  Parameter T_advance : jplan -> list I.t -> nat -> list positive -> cell V.t -> nat.
  Parameter T_go : nat -> jplan -> list I.t -> list positive -> list (cell V.t) ->
    list (list (cell V.t)) -> nat.
  (* spec: work_at *)
  Parameter work_at : jplan -> list I.t -> nat -> list positive -> nat.
  (* spec: participants *)
  Definition participants (p : jplan) (lvl : nat) : list nat :=
    filter (fun j => existsb (Nat.eqb lvl) (nth j (cols p) []))
      (seq 0 (length (cols p))).
  Parameter choose : jplan -> list I.t -> nat -> list positive -> option nat.
  Parameter T_choose : jplan -> list I.t -> nat -> list positive -> nat.
  (** The pivot is the least-degree participant, breaking equal-degree ties by position. *)
  Parameter choose_min : forall p ixs l pre ns j, nodes_ok p ixs l pre ns ->
    l < nvars p -> choose p ixs l ns = Some j ->
    In j (participants p l) /\ forall k, In k (participants p l) ->
      (I.degree (nth j ixs I.empty) (nth j ns 1%positive) <=
       I.degree (nth k ixs I.empty) (nth k ns 1%positive))%N /\
      (I.degree (nth j ixs I.empty) (nth j ns 1%positive) =
       I.degree (nth k ixs I.empty) (nth k ns 1%positive) -> j <= k).
  (** Every unfinished well-formed level has a pivot participant. *)
  Parameter choose_some : forall p ixs l pre ns, nodes_ok p ixs l pre ns ->
    l < nvars p -> exists j, choose p ixs l ns = Some j.
  (** Root nodes represent the initial empty assignment. *)
  Parameter nodes_ok_root : forall p ixs, wf_plan p ixs ->
    nodes_ok p ixs 0 [] (map I.root ixs).
  (** Successful probes extend every participating prefix. *)
  Parameter step_ok : forall p ixs l pre ns c ns', wf_plan p ixs ->
    nodes_ok p ixs l pre ns -> advance p ixs l ns c = Some ns' ->
    nodes_ok p ixs (S l) (c :: pre) ns'.
  (** A failed probe rules out all assignments extending that cell. *)
  Parameter advance_none : forall p ixs l pre ns c, wf_plan p ixs ->
    nodes_ok p ixs l pre ns -> advance p ixs l ns c = None ->
    forall b, firstn (S l) b = rev (c :: pre) -> ~ answer p ixs b.
  (** Recursive output comes from the accumulator or satisfies the current prefix. *)
  Parameter go_sound : forall p ixs l pre ns acc b, nodes_ok p ixs l pre ns ->
    In b (go (nvars p - l) p ixs ns pre acc) ->
    In b acc \/ (answer p ixs b /\ firstn l b = rev pre).
  (** Every answer extending the current prefix is emitted. *)
  Parameter go_complete : forall p ixs l pre ns acc b, nodes_ok p ixs l pre ns ->
    answer p ixs b -> firstn l b = rev pre ->
    In b (go (nvars p - l) p ixs ns pre acc).
  (** Disjoint answer prefixes and a duplicate-free accumulator give duplicate-free output. *)
  Parameter go_nodup : forall p ixs l pre ns acc, nodes_ok p ixs l pre ns ->
    NoDup acc ->
    (forall b, answer p ixs b -> firstn l b = rev pre -> ~ In b acc) ->
    NoDup (go (nvars p - l) p ixs ns pre acc).
  (** Public work starts at the root nodes. *)
  Parameter work_root : forall p ixs,
    work p ixs = work_at p ixs 0 (map I.root ixs).
  (** Finished assignments contribute one unit of recursive work. *)
  Parameter work_at_done : forall p ixs l ns, nvars p <= l ->
    work_at p ixs l ns = 1.
  (** A level pays for pivot enumeration, all probes and every surviving subtree. *)
  Parameter work_at_step : forall p ixs l pre ns j, nodes_ok p ixs l pre ns ->
    l < nvars p -> choose p ixs l ns = Some j ->
    work_at p ixs l ns = 1 + length (participants p l) *
      (1 + N.to_nat (I.degree (nth j ixs I.empty) (nth j ns 1%positive))) +
      fold_right Nat.add 0
        (map (fun c => match advance p ixs l ns c with
          | None => 0
          | Some ns' => work_at p ixs (S l) ns'
          end) (I.children (nth j ixs I.empty) (nth j ns 1%positive))).
  (** The public join starts recursion at the roots with an empty accumulator. *)
  Parameter run_go : forall p ixs,
    run p ixs = go (nvars p) p ixs (map I.root ixs) [] [].
  (** Recursive cost pays for probes and all surviving subtrees. *)
  Parameter T_go_le : forall p ixs l pre ns acc, nodes_ok p ixs l pre ns ->
    T_go (nvars p - l) p ixs ns pre acc <=
      c_join * (work_at p ixs l ns + 1) * (wmax p ixs + 1).
End JOIN_PLAN.

Module Type JOIN_ALL (V : VALUE_T) (I : INDEX_T V) := JOIN_T V I <+ JOIN_PLAN V I.
