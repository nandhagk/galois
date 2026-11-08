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

Module TarjanStateFacts.

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

Local Lemma lower_discovery v n s :
  Tarjan.disc (Tarjan.lower v n s) = Tarjan.disc s /\
    Tarjan.clock (Tarjan.lower v n s) = Tarjan.clock s.
Proof.
  rewrite Tarjan.lower_equation.
  destruct (Map.get positive_encoding v (Tarjan.low s)); split; reflexivity.
Qed.

Local Lemma edge_discovery u v k s :
  Tarjan.disc (Tarjan.edge u v k s) = Tarjan.disc s /\
    Tarjan.clock (Tarjan.edge u v k s) = Tarjan.clock s.
Proof.
  rewrite Tarjan.edge_equation. destruct k; try (split; reflexivity).
  all: destruct (FinSet.mem positive_encoding v (Tarjan.on_stack s));
    try (split; reflexivity).
  all: destruct (Map.get positive_encoding v (Tarjan.disc s));
    try (split; reflexivity).
  all: apply lower_discovery.
Qed.

Local Lemma emit_discovery root s :
  Tarjan.disc (Tarjan.emit root s) = Tarjan.disc s /\
    Tarjan.clock (Tarjan.emit root s) = Tarjan.clock s.
Proof.
  rewrite Tarjan.emit_equation. split; reflexivity.
Qed.

Local Lemma exit_discovery v parent s :
  Tarjan.disc (Tarjan.exit v parent s) = Tarjan.disc s /\
    Tarjan.clock (Tarjan.exit v parent s) = Tarjan.clock s.
Proof.
  rewrite Tarjan.exit_equation.
  destruct (Map.get positive_encoding v (Tarjan.low s)) as [l|];
    destruct (Map.get positive_encoding v (Tarjan.disc s)) as [d|]; try (split; reflexivity).
  destruct (Pos.eqb l d); [apply emit_discovery|].
  destruct parent; [apply lower_discovery|split; reflexivity].
Qed.

(** Discovery agreement relates Tarjan's numbers and clock to the same temporal search core. *)
Definition discovery_agrees {E} (c : SearchRun.core E) (s : Tarjan.state) :=
  Tarjan.disc s = SearchRun.pre_index c /\ Tarjan.clock s = SearchRun.pre_clock c.

(** Each shared event updates the search and Tarjan discovery indexes in the same way. *)
Theorem apply_discovery {E} (ev : Search.event E) c s :
  discovery_agrees c s ->
    discovery_agrees (SearchRun.core_event c ev) (Visitor.apply Tarjan.visitor ev s).
Proof.
  intros [Hdisc Hclock]. destruct ev as [v via|e u v k|v parent].
  - change (discovery_agrees (SearchRun.discover v via c) (Tarjan.enter v s)).
    rewrite SearchRun.discover_equation, Tarjan.enter_equation.
    unfold discovery_agrees. cbn [Tarjan.disc Tarjan.clock SearchRun.pre_index SearchRun.pre_clock].
    now rewrite Hdisc, Hclock.
  - change (discovery_agrees c (Tarjan.edge u v k s)).
    destruct (edge_discovery u v k s) as [Hd Hc].
    unfold discovery_agrees. now rewrite Hd, Hc.
  - change (discovery_agrees (SearchRun.finish v c) (Tarjan.exit v parent s)).
    destruct (exit_discovery v parent s) as [Hd Hc]. rewrite SearchRun.finish_equation.
    unfold discovery_agrees. cbn [SearchRun.pre_index SearchRun.pre_clock].
    now rewrite Hd, Hc.
Qed.

(** Discovery agreement holds for every prefix of one common event list. *)
Theorem events_discovery {E} (evs : list (Search.event E)) c s :
  discovery_agrees c s ->
  discovery_agrees (fold_left SearchRun.core_event evs c)
    (SearchRun.apply_events Tarjan.visitor evs s).
Proof.
  unfold SearchRun.apply_events. revert c s.
  induction evs as [|ev rest IH]; intros c s Hagree; [exact Hagree|].
  cbn [fold_left]. apply IH, apply_discovery, Hagree.
Qed.

(** Pending vertices, emitted members and owner bindings all have actual discovery numbers. *)
Record discovered (s : Tarjan.state) : Prop := Discovered {
  stack_discovered : forall v, In v (Tarjan.stack s) ->
    exists n, Map.get positive_encoding v (Tarjan.disc s) = Some n;
  emitted_discovered : forall v, In v (concat (Tarjan.emitted_rev s)) ->
    exists n, Map.get positive_encoding v (Tarjan.disc s) = Some n;
  owner_discovered : forall v i, Map.get positive_encoding v (Tarjan.owners s) = Some i ->
    exists n, Map.get positive_encoding v (Tarjan.disc s) = Some n
}.

Local Lemma set_present v (n : positive) (numbers : Map.t positive positive) x :
  Map.wf positive_encoding numbers ->
  (exists old, Map.get positive_encoding x numbers = Some old) ->
  exists number, Map.get positive_encoding x (Map.set positive_encoding v n numbers) =
    Some number.
Proof.
  intros Hwf [old Hold]. rewrite Map.get_set by exact Hwf.
  destruct (eqb positive_encoding x v); [now exists n|now exists old].
Qed.

(** Empty storage contains no undiscovered pending, emitted or owned vertices. *)
Theorem initial_discovered : discovered Tarjan.initial.
Proof.
  constructor.
  - intros v Hfalse. contradiction.
  - intros v Hfalse. contradiction.
  - intros v i Hfalse. change (Map.get positive_encoding v Map.empty = Some i) in Hfalse.
    rewrite Map.get_empty in Hfalse. discriminate.
Qed.

(** Entry provides discovery support even if an arbitrary event re-enters an existing vertex. *)
Theorem enter_discovered v s :
  storage s -> discovered s -> discovered (Tarjan.enter v s).
Proof.
  intros Hstorage Hdiscovered. rewrite Tarjan.enter_equation. constructor.
  - intros x [<-|Hx].
    + exists (Tarjan.clock s). apply Map.get_set_same, (disc_wf s Hstorage).
    + apply set_present; [exact (disc_wf s Hstorage)|].
      exact (stack_discovered s Hdiscovered x Hx).
  - intros x Hx. apply set_present; [exact (disc_wf s Hstorage)|].
    exact (emitted_discovered s Hdiscovered x Hx).
  - intros x i Hx. apply set_present; [exact (disc_wf s Hstorage)|].
    exact (owner_discovered s Hdiscovered x i Hx).
Qed.

Local Lemma lower_discovered v n s :
  discovered s -> discovered (Tarjan.lower v n s).
Proof.
  intro Hdiscovered. rewrite Tarjan.lower_equation.
  destruct (Map.get positive_encoding v (Tarjan.low s)); [|exact Hdiscovered].
  destruct Hdiscovered. constructor; assumption.
Qed.

Local Lemma edge_discovered u v k s :
  discovered s -> discovered (Tarjan.edge u v k s).
Proof.
  intro Hdiscovered. rewrite Tarjan.edge_equation. destruct k; try exact Hdiscovered.
  all: destruct (FinSet.mem positive_encoding v (Tarjan.on_stack s)); try exact Hdiscovered.
  all: destruct (Map.get positive_encoding v (Tarjan.disc s)); try exact Hdiscovered.
  all: now apply lower_discovered.
Qed.

(** Encoded membership tests reflect membership in a positive-ID list. *)
Theorem member_test x xs :
  existsb (eqb positive_encoding x) xs = true <-> In x xs.
Proof.
  rewrite existsb_exists. split.
  - intros [v [Hv Heq]].
    apply (eqb_true_iff positive_encoding positive_encoding_laws) in Heq.
    now subst v.
  - intro Hx. exists x. split; [exact Hx|apply eqb_refl].
Qed.

(** Emission can introduce owners only for already discovered vertices of its actual stack prefix. *)
Theorem emit_discovered root s :
  storage s -> discovered s -> discovered (Tarjan.emit root s).
Proof.
  intros Hstorage Hdiscovered.
  pose proof (pop_split root (Tarjan.next_component s) (Tarjan.stack s)
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s)) as [Hsplit _].
  pose proof (pop_owners root (Tarjan.next_component s) (Tarjan.stack s)
    (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s)) as Howners.
  rewrite Tarjan.emit_equation. constructor.
  - intros v Hv. apply (stack_discovered s Hdiscovered). rewrite Hsplit.
    apply in_or_app. now right.
  - intros v Hv. cbn [Tarjan.emitted_rev concat] in Hv. apply in_app_iff in Hv.
    destruct Hv as [Hmember|Hold].
    + apply (stack_discovered s Hdiscovered). rewrite Hsplit. apply in_or_app. now left.
    + exact (emitted_discovered s Hdiscovered v Hold).
  - intros v i Hget.
    cbn [Tarjan.owners] in Hget. rewrite Howners in Hget by exact (owners_wf s Hstorage).
    destruct (existsb (eqb positive_encoding v)
      (Tarjan.members (Tarjan.pop root (Tarjan.next_component s) (Tarjan.stack s)
        (Tarjan.low s) (Tarjan.on_stack s) (Tarjan.owners s)))) eqn:Hmember.
    + apply member_test in Hmember. apply (stack_discovered s Hdiscovered).
      rewrite Hsplit. apply in_or_app. now left.
    + exact (owner_discovered s Hdiscovered v i Hget).
Qed.

Local Lemma exit_discovered v parent s :
  storage s -> discovered s -> discovered (Tarjan.exit v parent s).
Proof.
  intros Hstorage Hdiscovered. rewrite Tarjan.exit_equation.
  destruct (Map.get positive_encoding v (Tarjan.low s)) as [l|];
    destruct (Map.get positive_encoding v (Tarjan.disc s)) as [d|]; try exact Hdiscovered.
  destruct (Pos.eqb l d); [now apply emit_discovered|].
  destruct parent; [now apply lower_discovered|exact Hdiscovered].
Qed.

(** Every callback preserves discovery support without a semantic or whole-trace premise. *)
Theorem apply_discovered {E} (ev : Search.event E) s :
  storage s -> discovered s -> discovered (Visitor.apply Tarjan.visitor ev s).
Proof.
  intros Hstorage Hdiscovered. destruct ev as [v via|e u v k|v parent].
  - change (discovered (Tarjan.enter v s)). now apply enter_discovered.
  - change (discovered (Tarjan.edge u v k s)). now apply edge_discovered.
  - change (discovered (Tarjan.exit v parent s)). now apply exit_discovered.
Qed.

(** Discovery support holds after every prefix of an arbitrary event list. *)
Theorem events_discovered {E} (evs : list (Search.event E)) s :
  storage s -> discovered s -> discovered (SearchRun.apply_events Tarjan.visitor evs s).
Proof.
  unfold SearchRun.apply_events. revert s.
  induction evs as [|ev rest IH]; intros s Hstorage Hdiscovered; [exact Hdiscovered|].
  cbn [fold_left]. apply IH.
  - now apply apply_storage.
  - now apply apply_discovered.
Qed.

(** Tarjan's final discovery map equals the actual search result's preorder-number map. *)
Theorem actual_discovery {V E} (p : Prepared.t V E) scope roots :
  Tarjan.disc (snd (Cost.value (SearchRun.run_c p Tarjan.visitor scope roots Tarjan.initial))) =
    Search.pre_num
      (fst (Cost.value (SearchRun.run_c p Tarjan.visitor scope roots Tarjan.initial))).
Proof.
  pose proof (events_discovery (SearchRun.events p scope roots) SearchRun.initial Tarjan.initial
    (conj eq_refl eq_refl)) as Hagree.
  rewrite SearchRun.run_events.
  unfold SearchRun.result_of. rewrite SearchRun.result_equation.
  exact (proj1 Hagree).
Qed.

(** Discovery numbering on the actual visitor state is exact for arbitrary scopes and roots. *)
Theorem discovery_index {V E} (p : Prepared.t V E) scope roots v i :
  Prepared.ready p ->
  (Map.get positive_encoding v
    (Tarjan.disc (snd (Cost.value
      (SearchRun.run_c p Tarjan.visitor scope roots Tarjan.initial)))) = Some i <->
    nth_error (Search.preorder (fst (Cost.value
      (SearchRun.run_c p Tarjan.visitor scope roots Tarjan.initial))))
      (Nat.pred (Pos.to_nat i)) = Some v).
Proof.
  intro Hready. rewrite actual_discovery.
  apply (Search.pre_num_index _ _ _ _ (SearchExact.run_exact p Tarjan.visitor
    scope roots Tarjan.initial Hready)).
Qed.

(** The actual visitor state has discovery support for all pending, emitted and owned vertices. *)
Theorem actual_discovered {V E} (p : Prepared.t V E) scope roots :
  discovered (snd (Cost.value (SearchRun.run_c p Tarjan.visitor scope roots Tarjan.initial))).
Proof.
  rewrite SearchRun.run_events. apply events_discovered; [apply initial_storage|].
  apply initial_discovered.
Qed.

Local Lemma discovered_reachable {V E} (p : Prepared.t V E) scope roots v number :
  Prepared.ready p ->
  Map.get positive_encoding v
    (Tarjan.disc (snd (Cost.value
      (SearchRun.run_c p Tarjan.visitor scope roots Tarjan.initial)))) = Some number ->
  Search.scoped_reachable p scope roots v.
Proof.
  intros Hready Hnumber.
  apply (proj1 (discovery_index p scope roots v number Hready)) in Hnumber.
  apply nth_error_In in Hnumber.
  exact (proj1 (Search.pre_complete _ _ _ _
    (SearchExact.run_exact p Tarjan.visitor scope roots Tarjan.initial Hready) v) Hnumber).
Qed.

(** Every returned owner binding belongs to the admitted reachable region of the same actual run. *)
Theorem owners_reachable {V E} (p : Prepared.t V E) scope roots v i :
  Prepared.ready p ->
  Map.get positive_encoding v (Scc.comp_of (Tarjan.compute p scope roots)) = Some i ->
    Search.scoped_reachable p scope roots v.
Proof.
  intros Hready Howner. rewrite Tarjan.compute_equation, Tarjan.result_equation in Howner.
  cbn [Scc.comp_of] in Howner.
  destruct (owner_discovered _ (actual_discovered p scope roots) v i Howner)
    as [number Hnumber].
  exact (discovered_reachable p scope roots v number Hready Hnumber).
Qed.

(** Every emitted component member belongs to the admitted reachable region of the actual run. *)
Theorem components_reachable {V E} (p : Prepared.t V E) scope roots v :
  Prepared.ready p -> In v (concat (Scc.components (Tarjan.compute p scope roots))) ->
    Search.scoped_reachable p scope roots v.
Proof.
  intros Hready Hin. rewrite Tarjan.compute_equation, Tarjan.result_equation in Hin.
  cbn [Scc.components] in Hin. apply in_concat in Hin.
  destruct Hin as [c [Hc Hv]]. apply (proj2 (in_rev _ _)) in Hc.
  assert (Hemitted : In v (concat (Tarjan.emitted_rev (snd (Cost.value
    (SearchRun.run_c p Tarjan.visitor scope roots Tarjan.initial)))))).
  { apply in_concat. exists c. auto. }
  destruct (emitted_discovered _ (actual_discovered p scope roots) v Hemitted)
    as [number Hnumber].
  exact (discovered_reachable p scope roots v number Hready Hnumber).
Qed.

Local Lemma scoped_target {V E} (p : Prepared.t V E) scope u es v :
  Search.scoped_path p scope u es v ->
    Prepared.valid_id p v /\ Scope.admits scope v = true.
Proof.
  intro Hpath. induction Hpath; tauto.
Qed.

(** Rejected vertices have no computed component owner for arbitrary supplied roots. *)
Theorem rejected_unowned {V E} (p : Prepared.t V E) scope roots v :
  Prepared.ready p -> Scope.admits scope v = false ->
    Map.get positive_encoding v (Scc.comp_of (Tarjan.compute p scope roots)) = None.
Proof.
  intros Hready Hrejected.
  destruct (Map.get positive_encoding v (Scc.comp_of (Tarjan.compute p scope roots)))
    as [i|] eqn:Howner; [|reflexivity].
  destruct (owners_reachable p scope roots v i Hready Howner) as [root [es [_ Hpath]]].
  pose proof (proj2 (scoped_target p scope root es v Hpath)) as Hadmitted.
  congruence.
Qed.

(** Unknown IDs have no computed component owner even if the scope admits them. *)
Theorem unknown_unowned {V E} (p : Prepared.t V E) scope roots v :
  Prepared.ready p -> ~ Prepared.valid_id p v ->
    Map.get positive_encoding v (Scc.comp_of (Tarjan.compute p scope roots)) = None.
Proof.
  intros Hready Hunknown.
  destruct (Map.get positive_encoding v (Scc.comp_of (Tarjan.compute p scope roots)))
    as [i|] eqn:Howner; [|reflexivity].
  destruct (owners_reachable p scope roots v i Hready Howner) as [root [es [_ Hpath]]].
  exfalso. apply Hunknown. exact (proj1 (scoped_target p scope root es v Hpath)).
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

(** Empty supplied roots return no components and no owner bindings on every prepared record. *)
Theorem compute_empty {V E} (p : Prepared.t V E) scope :
  Tarjan.compute p scope [] = Scc.Result [] Map.empty.
Proof.
  reflexivity.
Qed.

(** The full SCC specification holds for empty roots without any readiness restriction. *)
Theorem empty_roots_exact {V E} (p : Prepared.t V E) scope :
  Scc.exact p scope [] (Tarjan.compute p scope []).
Proof.
  rewrite compute_empty. constructor.
  - constructor.
  - constructor.
  - intro v. split; [contradiction|].
    intros [root [es [Hfalse _]]]. contradiction.
  - apply Map.wf_empty.
  - intros v i. cbn [Scc.comp_of Scc.components]. rewrite Map.get_empty.
    split; [discriminate|].
    intros [c [Hnth _]]. rewrite nth_error_nil in Hnth. discriminate.
  - intros u e v i j _ Hfalse.
    change (Map.get positive_encoding u Map.empty = Some i) in Hfalse.
    rewrite Map.get_empty in Hfalse. discriminate.
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

End TarjanStateFacts.
