(** * Tarjan stack and trace guarantees

    Stack lemmas describe the exact prefix transferred to a component by the visitor.
    For example, popping at the stack root leaves its older suffix untouched.
    Builds on: GraphTarjan and the public search trace guarantees. *)

From Stdlib Require Import List Bool PArith NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Graph Require Import GraphPrepared GraphVisitor GraphSearchSpec GraphSearch
  GraphSearchExact GraphSccSpec GraphTarjan.
Import List.ListNotations.

Module TarjanExact.

(** Popping partitions the actual input stack into the consumed prefix and surviving suffix. *)
Theorem pop_split root i xs lows active own :
  let answer := Tarjan.pop root i xs lows active own in
  xs = Tarjan.members answer ++ Tarjan.tail answer /\
    (In root xs -> In root (Tarjan.members answer)).
Proof.
  revert lows active own. induction xs as [|v rest IH]; intros lows active own;
    rewrite Tarjan.pop_equation; [cbn; tauto|].
  destruct (Map.code_compare v root) eqn:Hcompare; cbn [Tarjan.members Tarjan.tail].
  - apply Map.code_compare_eq in Hcompare. subst v. cbn. split; [reflexivity|auto].
  - destruct (IH (Map.remove positive_encoding v lows)
      (FinSet.remove positive_encoding v active) (Map.set positive_encoding v i own))
      as [Hsplit Hroot].
    cbn [app In]. rewrite <- Hsplit. split; [reflexivity|intuition].
  - destruct (IH (Map.remove positive_encoding v lows)
      (FinSet.remove positive_encoding v active) (Map.set positive_encoding v i own))
      as [Hsplit Hroot].
    cbn [app In]. rewrite <- Hsplit. split; [reflexivity|intuition].
Qed.

(** Popping a nonempty stack always emits a nonempty prefix. *)
Theorem pop_nonempty root i v rest lows active own :
  Tarjan.members (Tarjan.pop root i (v :: rest) lows active own) <> [].
Proof.
  rewrite Tarjan.pop_equation. destruct (Map.code_compare v root); discriminate.
Qed.

(** A stack split at its first root occurrence has precisely that prefix as its component. *)
Theorem pop_prefix root i prefix suffix lows active own :
  ~ In root prefix ->
  Tarjan.members (Tarjan.pop root i (prefix ++ root :: suffix) lows active own) =
    prefix ++ [root] /\
  Tarjan.tail (Tarjan.pop root i (prefix ++ root :: suffix) lows active own) = suffix.
Proof.
  revert lows active own. induction prefix as [|v rest IH]; intros lows active own Hnot.
  - cbn [app]. rewrite Tarjan.pop_equation.
    rewrite (proj2 (Map.code_compare_eq root root) eq_refl). split; reflexivity.
  - cbn [app]. rewrite Tarjan.pop_equation.
    destruct (Map.code_compare v root) eqn:Hcompare.
    + apply Map.code_compare_eq in Hcompare. subst v. exfalso. apply Hnot. now left.
    + cbn [Tarjan.members Tarjan.tail].
      destruct (IH (Map.remove positive_encoding v lows)
        (FinSet.remove positive_encoding v active) (Map.set positive_encoding v i own)
        ltac:(intro Hin; apply Hnot; now right)) as [Hmembers Htail].
      rewrite Hmembers, Htail. split; reflexivity.
    + cbn [Tarjan.members Tarjan.tail].
      destruct (IH (Map.remove positive_encoding v lows)
        (FinSet.remove positive_encoding v active) (Map.set positive_encoding v i own)
        ltac:(intro Hin; apply Hnot; now right)) as [Hmembers Htail].
      rewrite Hmembers, Htail. split; reflexivity.
Qed.

(** Pop operations preserve canonical map and set storage for arbitrary input stacks. *)
Theorem pop_wf root i xs lows active own :
  Map.wf positive_encoding lows -> FinSet.wf positive_encoding active ->
  Map.wf positive_encoding own ->
  let answer := Tarjan.pop root i xs lows active own in
  Map.wf positive_encoding (Tarjan.links answer) /\
  FinSet.wf positive_encoding (Tarjan.pending answer) /\
  Map.wf positive_encoding (Tarjan.component_owners answer).
Proof.
  revert lows active own. induction xs as [|v rest IH]; intros lows active own Hl Ha Ho;
    rewrite Tarjan.pop_equation; [auto|].
  pose proof (Map.wf_remove positive_encoding v lows Hl) as Hl'.
  pose proof (FinSet.wf_remove positive_encoding v active Ha) as Ha'.
  pose proof (Map.wf_set positive_encoding v i own Ho) as Ho'.
  destruct (Map.code_compare v root); cbn [Tarjan.links Tarjan.pending Tarjan.component_owners].
  - auto.
  - exact (IH _ _ _ Hl' Ha' Ho').
  - exact (IH _ _ _ Hl' Ha' Ho').
Qed.

(** Popping assigns the new component to precisely the consumed prefix and keeps other owners. *)
Theorem pop_owners root i xs lows active own x :
  Map.wf positive_encoding own ->
  Map.get positive_encoding x
    (Tarjan.component_owners (Tarjan.pop root i xs lows active own)) =
    if existsb (eqb positive_encoding x)
      (Tarjan.members (Tarjan.pop root i xs lows active own))
    then Some i else Map.get positive_encoding x own.
Proof.
  revert lows active own. induction xs as [|v rest IH]; intros lows active own Hwf;
    rewrite Tarjan.pop_equation; [reflexivity|].
  destruct (Map.code_compare v root);
    cbn [Tarjan.component_owners Tarjan.members existsb].
  - rewrite Map.get_set by exact Hwf.
    destruct (eqb positive_encoding x v); reflexivity.
  - rewrite IH by now apply Map.wf_set.
    rewrite Map.get_set by exact Hwf.
    destruct (eqb positive_encoding x v);
      destruct (existsb (eqb positive_encoding x)
        (Tarjan.members (Tarjan.pop root i rest (Map.remove positive_encoding v lows)
          (FinSet.remove positive_encoding v active) (Map.set positive_encoding v i own))));
      reflexivity.
  - rewrite IH by now apply Map.wf_set.
    rewrite Map.get_set by exact Hwf.
    destruct (eqb positive_encoding x v);
      destruct (existsb (eqb positive_encoding x)
        (Tarjan.members (Tarjan.pop root i rest (Map.remove positive_encoding v lows)
          (FinSet.remove positive_encoding v active) (Map.set positive_encoding v i own))));
      reflexivity.
Qed.

(** Popping removes low links at precisely its consumed keys and keeps every other binding. *)
Theorem pop_links root i xs lows active own x :
  Map.get positive_encoding x (Tarjan.links (Tarjan.pop root i xs lows active own)) =
    if existsb (eqb positive_encoding x)
      (Tarjan.members (Tarjan.pop root i xs lows active own))
    then None else Map.get positive_encoding x lows.
Proof.
  revert lows active own. induction xs as [|v rest IH]; intros lows active own;
    rewrite Tarjan.pop_equation; [reflexivity|].
  destruct (Map.code_compare v root); cbn [Tarjan.links Tarjan.members existsb].
  - rewrite Map.get_remove.
    destruct (eqb positive_encoding x v); reflexivity.
  - rewrite IH, Map.get_remove.
    destruct (eqb positive_encoding x v);
      destruct (existsb (eqb positive_encoding x)
        (Tarjan.members (Tarjan.pop root i rest (Map.remove positive_encoding v lows)
          (FinSet.remove positive_encoding v active) (Map.set positive_encoding v i own))));
      reflexivity.
  - rewrite IH, Map.get_remove.
    destruct (eqb positive_encoding x v);
      destruct (existsb (eqb positive_encoding x)
        (Tarjan.members (Tarjan.pop root i rest (Map.remove positive_encoding v lows)
          (FinSet.remove positive_encoding v active) (Map.set positive_encoding v i own))));
      reflexivity.
Qed.

(** Popping removes precisely its consumed keys from the on-stack set. *)
Theorem pop_pending root i xs lows active own x :
  FinSet.mem positive_encoding x (Tarjan.pending (Tarjan.pop root i xs lows active own)) =
    (negb (existsb (eqb positive_encoding x)
      (Tarjan.members (Tarjan.pop root i xs lows active own))) &&
      FinSet.mem positive_encoding x active)%bool.
Proof.
  revert lows active own. induction xs as [|v rest IH]; intros lows active own;
    rewrite Tarjan.pop_equation; [reflexivity|].
  destruct (Map.code_compare v root); cbn [Tarjan.pending Tarjan.members existsb].
  - rewrite FinSet.mem_remove.
    destruct (eqb positive_encoding x v); reflexivity.
  - rewrite IH, FinSet.mem_remove.
    destruct (eqb positive_encoding x v);
      destruct (existsb (eqb positive_encoding x)
        (Tarjan.members (Tarjan.pop root i rest (Map.remove positive_encoding v lows)
          (FinSet.remove positive_encoding v active) (Map.set positive_encoding v i own))));
      destruct (FinSet.mem positive_encoding x active); reflexivity.
  - rewrite IH, FinSet.mem_remove.
    destruct (eqb positive_encoding x v);
      destruct (existsb (eqb positive_encoding x)
        (Tarjan.members (Tarjan.pop root i rest (Map.remove positive_encoding v lows)
          (FinSet.remove positive_encoding v active) (Map.set positive_encoding v i own))));
      destruct (FinSet.mem positive_encoding x active); reflexivity.
Qed.

(** Computational storage invariants are independent of graph and SCC semantic invariants. *)
Record storage (s : Tarjan.state) : Prop := Storage {
  disc_wf : Map.wf positive_encoding (Tarjan.disc s);
  low_wf : Map.wf positive_encoding (Tarjan.low s);
  stack_set_wf : FinSet.wf positive_encoding (Tarjan.on_stack s);
  owners_wf : Map.wf positive_encoding (Tarjan.owners s)
}.

(** Initial visitor maps and its pending set are canonical empty containers. *)
Theorem initial_storage : storage Tarjan.initial.
Proof.
  constructor; [apply Map.wf_empty|apply Map.wf_empty|apply FinSet.wf_empty|apply Map.wf_empty].
Qed.

(** Entry preserves canonical storage for every ID, including a repeated ID. *)
Theorem enter_storage v s : storage s -> storage (Tarjan.enter v s).
Proof.
  intros [Hd Hl Ha Ho]. rewrite Tarjan.enter_equation. constructor; cbn.
  - now apply Map.wf_set.
  - now apply Map.wf_set.
  - now apply FinSet.wf_add.
  - exact Ho.
Qed.

(** Lowering preserves canonical storage and does not create a missing low-link entry. *)
Theorem lower_storage v n s : storage s -> storage (Tarjan.lower v n s).
Proof.
  intro Hstorage. rewrite Tarjan.lower_equation.
  destruct (Map.get positive_encoding v (Tarjan.low s)); [|exact Hstorage].
  destruct Hstorage as [Hd Hl Ha Ho]. constructor; cbn; auto using Map.wf_set.
Qed.

(** Every edge class preserves canonical storage independently of event validity. *)
Theorem edge_storage u v k s : storage s -> storage (Tarjan.edge u v k s).
Proof.
  intro Hstorage. rewrite Tarjan.edge_equation.
  destruct k; try exact Hstorage.
  all: destruct (FinSet.mem positive_encoding v (Tarjan.on_stack s)); try exact Hstorage.
  all: destruct (Map.get positive_encoding v (Tarjan.disc s)); try exact Hstorage.
  all: now apply lower_storage.
Qed.

(** Emission preserves canonical storage by updating exactly the real popped keys. *)
Theorem emit_storage root s : storage s -> storage (Tarjan.emit root s).
Proof.
  intros [Hd Hl Ha Ho]. rewrite Tarjan.emit_equation.
  destruct (pop_wf root (Tarjan.next_component s) (Tarjan.stack s)
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s) Hl Ha Ho) as [Hl' [Ha' Ho']].
  constructor; assumption.
Qed.

(** Exit preserves canonical storage in both the component and parent-propagation branches. *)
Theorem exit_storage v parent s : storage s -> storage (Tarjan.exit v parent s).
Proof.
  intro Hstorage. rewrite Tarjan.exit_equation.
  destruct (Map.get positive_encoding v (Tarjan.low s)) as [l|];
    destruct (Map.get positive_encoding v (Tarjan.disc s)) as [d|]; try exact Hstorage.
  destruct (Pos.eqb l d); [now apply emit_storage|].
  destruct parent; [now apply lower_storage|exact Hstorage].
Qed.

(** All visitor callbacks preserve canonical storage on arbitrary event lists. *)
Theorem apply_storage {E} (ev : Search.event E) s :
  storage s -> storage (Visitor.apply Tarjan.visitor ev s).
Proof.
  intro Hstorage. destruct ev as [v via|e u v k|v parent].
  - change (storage (Tarjan.enter v s)). now apply enter_storage.
  - change (storage (Tarjan.edge u v k s)). now apply edge_storage.
  - change (storage (Tarjan.exit v parent s)). now apply exit_storage.
Qed.

(** Folding any event prefix preserves the initial canonical storage invariant. *)
Theorem events_storage {E} (evs : list (Search.event E)) s :
  storage s -> storage (SearchRun.apply_events Tarjan.visitor evs s).
Proof.
  unfold SearchRun.apply_events. revert s.
  induction evs as [|ev rest IH]; intros s Hstorage; [exact Hstorage|].
  cbn [fold_left]. apply IH, apply_storage, Hstorage.
Qed.

(** The computation folds the actual shared-search event list, without a separate traversal. *)
Theorem compute_events {V E} (p : Prepared.t V E) scope roots :
  Tarjan.compute p scope roots =
    Tarjan.result (SearchRun.apply_events Tarjan.visitor
      (SearchRun.events p scope roots) Tarjan.initial).
Proof.
  rewrite Tarjan.compute_equation, SearchRun.run_events. reflexivity.
Qed.

(** Every computed owner map has canonical storage, even for a malformed prepared input. *)
Theorem compute_owners_wf {V E} (p : Prepared.t V E) scope roots :
  Map.wf positive_encoding (Scc.comp_of (Tarjan.compute p scope roots)).
Proof.
  rewrite compute_events, Tarjan.result_equation. cbn [Scc.comp_of].
  apply owners_wf, events_storage, initial_storage.
Qed.

(** The Tarjan visitor and the temporal trace share the same actual search result and final core. *)
Theorem compute_trace {V E} (p : Prepared.t V E) scope roots :
  Prepared.ready p ->
  exists final,
    fst (Cost.value (SearchRun.run_c p Tarjan.visitor scope roots Tarjan.initial)) =
      SearchRun.result final /\
    SearchRun.trace_roots p scope roots SearchRun.initial
      (SearchRun.events p scope roots) final /\
    Tarjan.compute p scope roots =
      Tarjan.result (SearchRun.apply_events Tarjan.visitor
        (SearchRun.events p scope roots) Tarjan.initial).
Proof.
  intro Hready. destruct (SearchExact.events_wf p scope roots Hready)
    as [final [Hresult Htrace]].
  exists final. split.
  - rewrite SearchRun.run_result. exact Hresult.
  - split; [exact Htrace|apply compute_events].
Qed.

End TarjanExact.
