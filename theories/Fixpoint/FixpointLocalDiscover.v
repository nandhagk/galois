(** * Indexed dependency discovery

    A depth-first stack expands each unknown and constraint once.
    For example, a side contributor brings its nominal target and its reads into the region.
    Builds on: FixpointIndex, BaseSet and CostLoop. *)

From Stdlib Require Import List Bool Arith NArith PArith Lia.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseEncoding BaseCode BaseEq BaseMap BaseSet.
From Galois.Fixpoint Require Import FixpointSystem FixpointIndex FixpointAnalysis.
Import List.ListNotations Cost.Notations.

Module LocalDiscover.

(** Visited vertices suppress repeated expansion while the stack retains incidence multiplicity. *)
Record state (V : Type) := State {
  visited : FinSet.t V;
  pending : list V
}.

Arguments State {V}.
Arguments visited {V}.
Arguments pending {V}.

(** Adjacency follows contributors backwards and then every declared output and read forwards. *)
Definition adjacent_c {X C A} (a : Analysis.t X C A) (ix : sys_index X C)
    (v : X + C) : Cost.t (list (X + C)) :=
  match v with
  | inl x =>
    let* cs := contributors_of_c (Analysis.key_enc a) ix x in
    map_c (fun c => Cost.ret (inr c)) cs
  | inr c =>
    Cost.step ;;
    let* target := System.target_c (Analysis.system a) c in
    Cost.step ;;
    let* sides := System.side_targets_c (Analysis.static a) c in
    Cost.step ;;
    let* reads := System.deps_c (Analysis.static a) c in
    let* rest := app_c sides reads in
    map_c (fun x => Cost.ret (inl x)) (target :: rest)
  end.

Definition adjacent {X C A} (a : Analysis.t X C A) ix v :=
  Cost.value (adjacent_c a ix v).

(** A stack probe stops on emptiness or expands the first vertex that has not been visited. *)
Definition step_c {V} (EV : encoding V) (next : V -> Cost.t (list V)) (s : state V)
    : Cost.t (state V + FinSet.t V) :=
  match pending s with
  | [] => Cost.ret (inr (visited s))
  | v :: rest =>
    let* seen := FinSet.mem_c EV v (visited s) in
    if seen then Cost.ret (inl (State (visited s) rest))
    else
      let* marked := FinSet.add_c EV v (visited s) in
      Cost.step ;;
      let* neighbors := next v in
      let* todo := app_c neighbors rest in
      Cost.ret (inl (State marked todo))
  end.

Definition step {V} EV next s := Cost.value (@step_c V EV next s).

(** Discovery uses caller fuel without inspecting termination evidence for lattice iteration. *)
Definition run_c {X C A} (a : Analysis.t X C A) ix roots fuel :=
  let* entries := map_c (fun x => Cost.ret (@inl X C x)) roots in
  iterate (step_c (sum_encoding (Analysis.key_enc a) (Analysis.row_enc a))
    (adjacent_c a ix)) fuel (State FinSet.empty entries).

Definition run {X C A} (a : Analysis.t X C A) ix roots fuel :=
  Cost.value (run_c a ix roots fuel).

(** The pure adjacency equation retains duplicate metadata and index occurrences. *)
Theorem adjacent_equation {X C A} (a : Analysis.t X C A) ix v :
  adjacent a ix v =
    match v with
    | inl x => map (@inr X C) (contributors_of (Analysis.key_enc a) ix x)
    | inr c => map (@inl X C) (System.target (Analysis.system a) c ::
      side_targets (Analysis.static a) c ++ deps (Analysis.static a) c)
    end.
Proof.
  destruct v; unfold adjacent, adjacent_c; autorewrite with galois_cost; reflexivity.
Qed.

(** Stack transitions expose membership and the returned adjacency list through public values. *)
Theorem step_equation {V} EV next (s : state V) :
  step EV next s =
    match pending s with
    | [] => inr (visited s)
    | v :: rest =>
      if FinSet.mem EV v (visited s) then inl (State (visited s) rest)
      else inl (State (FinSet.add EV v (visited s)) (Cost.value (next v) ++ rest))
    end.
Proof.
  unfold step, step_c; destruct (pending s); autorewrite with galois_cost.
  - reflexivity.
  - fold (FinSet.mem EV v (visited s)).
    destruct (FinSet.mem EV v (visited s)); autorewrite with galois_cost; reflexivity.
Qed.

(** A closed region contains roots and every neighbor of each of its vertices. *)
Definition closed {V} (next : V -> list V) (roots : list V) (region : V -> Prop) : Prop :=
  (forall v, In v roots -> region v) /\
  forall v w, region v -> In w (next v) -> region w.

(** The frontier holds every root or neighbor that has not yet been marked. *)
Definition frontier {V} (EV : encoding V) (next : V -> list V) roots (s : state V) :=
  FinSet.wf EV (visited s) /\
  (forall v, In v roots -> FinSet.mem EV v (visited s) = true \/ In v (pending s)) /\
  forall v w, FinSet.mem EV v (visited s) = true -> In w (next v) ->
    FinSet.mem EV w (visited s) = true \/ In w (pending s).

Local Lemma marked_member {V} (EV : encoding V) (HE : encoding_laws EV) v w marked :
  FinSet.wf EV marked ->
  FinSet.mem EV w (FinSet.add EV v marked) = true <->
    w = v \/ FinSet.mem EV w marked = true.
Proof.
  intro Hwf; rewrite FinSet.mem_add by exact Hwf.
  rewrite orb_true_iff, (eqb_true_iff EV HE); reflexivity.
Qed.

Local Lemma frontier_next {V} EV (HE : encoding_laws EV) next roots (s t : state V) :
  frontier EV (fun v => Cost.value (next v)) roots s ->
  step EV next s = inl t ->
  frontier EV (fun v => Cost.value (next v)) roots t.
Proof.
  intros [Hwf [Hroots Hneighbors]] Hstep; rewrite step_equation in Hstep.
  destruct (pending s) as [|v rest] eqn:Htodo; [discriminate|].
  destruct (FinSet.mem EV v (visited s)) eqn:Hseen; injection Hstep as <-;
    cbn [visited pending].
  - split; [exact Hwf|]; split.
    + intros w Hw; destruct (Hroots w Hw) as [Hw'|Hw']; [now left|].
      destruct Hw' as [<-|Hw']; [now left|now right].
    + intros w u Hw Hu; destruct (Hneighbors w u Hw Hu) as [Hu'|Hu']; [now left|].
      destruct Hu' as [<-|Hu']; [now left|now right].
  - split; [apply FinSet.wf_add, Hwf|]; split.
    + intros w Hw; destruct (Hroots w Hw) as [Hw'|Hw'].
      * left; apply marked_member; [exact HE|exact Hwf|now right].
      * destruct Hw' as [<-|Hw'].
        -- left; apply marked_member; [exact HE|exact Hwf|now left].
        -- right; apply in_or_app; now right.
    + intros w u Hw Hu; apply (marked_member EV HE v w _ Hwf) in Hw.
      destruct Hw as [<-|Hw].
      * right; apply in_or_app; now left.
      * destruct (Hneighbors w u Hw Hu) as [Hu'|Hu'].
        -- left; apply marked_member; [exact HE|exact Hwf|now right].
        -- destruct Hu' as [<-|Hu'].
           ++ left; apply marked_member; [exact HE|exact Hwf|now left].
           ++ right; apply in_or_app; now right.
Qed.

Local Lemma frontier_stop {V} EV next roots (s : state V) region :
  frontier EV (fun v => Cost.value (next v)) roots s ->
  step EV next s = inr region ->
  FinSet.wf EV region /\
    closed (fun v => Cost.value (next v)) roots (fun v => FinSet.mem EV v region = true).
Proof.
  intros [Hwf [Hroots Hneighbors]] Hstep; rewrite step_equation in Hstep.
  destruct (pending s) as [|v rest] eqn:Htodo.
  - injection Hstep as <-; split; [exact Hwf|]; split.
    + intros v Hv; destruct (Hroots v Hv) as [Hv'|Hv']; [exact Hv'|].
      contradiction.
    + intros v w Hv Hw; destruct (Hneighbors v w Hv Hw) as [Hw'|Hw']; [exact Hw'|].
      contradiction.
  - destruct (FinSet.mem EV v (visited s)); discriminate.
Qed.

(** Every completed depth-first discovery returns a well-formed closed region. *)
Theorem completed_closed {V} (EV : encoding V) (HE : encoding_laws EV)
    next roots fuel region :
  Cost.value (iterate (step_c EV next) fuel (State FinSet.empty roots)) = inr region ->
  FinSet.wf EV region /\
    closed (fun v => Cost.value (next v)) roots (fun v => FinSet.mem EV v region = true).
Proof.
  intro Hloop; pose proof (iterate_value (step_c EV next) fuel
    (State FinSet.empty roots)) as Hrun; rewrite Hloop in Hrun.
  clear Hloop.
  assert (Hinitial : frontier EV (fun v => Cost.value (next v)) roots
    (State FinSet.empty roots)).
  { split; [apply FinSet.wf_empty|]; cbn [visited pending]; split.
    - intros v Hv; now right.
    - intros v w Hv; rewrite FinSet.mem_empty in Hv; discriminate. }
  remember (inr region) as result eqn:Hresult in Hrun.
  revert Hinitial; induction Hrun as [s|n s r Hstop|n s t result Hnext Hrun IH].
  - discriminate.
  - injection Hresult as <-; intro HI; eapply frontier_stop; eassumption.
  - intro HI; apply IH; [exact Hresult|].
    eapply frontier_next; eassumption.
Qed.

(** Membership discovered by the stack belongs to every closed region containing its roots. *)
Theorem completed_least {V} (EV : encoding V) (HE : encoding_laws EV)
    next roots fuel region P :
  closed (fun v => Cost.value (next v)) roots P ->
  Cost.value (iterate (step_c EV next) fuel (State FinSet.empty roots)) = inr region ->
  forall v, FinSet.mem EV v region = true -> P v.
Proof.
  intros [Hroots Hclosed] Hloop.
  pose proof (iterate_value (step_c EV next) fuel (State FinSet.empty roots)) as Hrun.
  rewrite Hloop in Hrun.
  clear Hloop.
  set (safe := fun s : state V =>
    FinSet.wf EV (visited s) /\
    (forall v, FinSet.mem EV v (visited s) = true -> P v) /\
    (forall v, In v (pending s) -> P v)).
  assert (Hinitial : safe (State FinSet.empty roots)).
  { cbn [safe visited pending]; split; [apply FinSet.wf_empty|]; split.
    - intros v Hv; cbn [visited] in Hv; rewrite FinSet.mem_empty in Hv; discriminate.
    - exact Hroots. }
  remember (inr region) as result eqn:Hresult in Hrun.
  revert Hinitial; induction Hrun as [s|n s r Hstop|n s t result Hnext Hrun IH];
    intros [Hwf [Hmarked Htodo]].
  - discriminate.
  - injection Hresult as <-; fold (step EV next s) in Hstop.
    rewrite step_equation in Hstop.
    destruct (pending s) as [|v rest]; [injection Hstop as <-; exact Hmarked|].
    destruct (FinSet.mem EV v (visited s)); discriminate.
  - apply IH; [exact Hresult|]; fold (step EV next s) in Hnext.
    rewrite step_equation in Hnext.
    destruct (pending s) as [|v rest] eqn:Hstack; [discriminate|].
    destruct (FinSet.mem EV v (visited s)) eqn:Hseen; injection Hnext as <-;
      cbn [visited pending].
    + split; [exact Hwf|]; split; [exact Hmarked|].
      intros w Hw; apply Htodo; now right.
    + split; [apply FinSet.wf_add, Hwf|]; split.
      * intros w Hw; apply (marked_member EV HE v w _ Hwf) in Hw.
        destruct Hw as [<-|Hw].
        -- apply Htodo; now left.
        -- apply Hmarked, Hw.
      * intros w Hw; apply in_app_or in Hw; destruct Hw as [Hw|Hw].
        -- eapply Hclosed; [apply Htodo; now left|exact Hw].
        -- apply Htodo; now right.
Qed.

End LocalDiscover.
Import LocalDiscover.
