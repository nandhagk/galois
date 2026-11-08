(** * Hierarchy domain transport

    Equivalent admission and root predicates transport exact forests without changing their data.
    For example, reversing the supplied child roots keeps the same rooted component domain.
    Builds on: GraphHierSpec, GraphHier and the raw finite-set update law. *)

From Stdlib Require Import List Bool PArith.
From Galois.Base Require Import BaseEncoding BaseEq BaseSet.
From Galois.Graph Require Import GraphPrepared GraphVisitor GraphSearchSpec GraphSccSpec
  GraphHierSpec GraphHier GraphTarjanState.
Import List.ListNotations.

Module HierTransport.

(** Pointwise admission equality transports every labelled scoped path. *)
Theorem path_scope {V E} (p : Prepared.t V E) source target u es v :
  (forall x, Scope.admits source x = Scope.admits target x) ->
  Search.scoped_path p source u es v -> Search.scoped_path p target u es v.
Proof.
  intros Hequiv Hpath.
  induction Hpath as [v Hv Ha|u e v es z Hu Ha Harc Htail IH].
  - apply Search.scoped_nil; [exact Hv|now rewrite <- Hequiv].
  - eapply Search.scoped_cons; [exact Hu|now rewrite <- Hequiv|exact Harc|exact IH].
Qed.

(** Equivalent admission and root membership give equivalent rooted scoped reachability. *)
Theorem reachable {V E} (p : Prepared.t V E) source roots target other v :
  (forall x, Scope.admits source x = Scope.admits target x) ->
  (forall x, In x roots <-> In x other) ->
  (Search.scoped_reachable p source roots v <->
    Search.scoped_reachable p target other v).
Proof.
  intros Hscope Hroots. split; intros [r [es [Hr Hpath]]]; exists r, es; split.
  - now apply Hroots.
  - exact (path_scope p source target r es v Hscope Hpath).
  - now apply Hroots.
  - apply (path_scope p target source r es v); [intro x; symmetry; apply Hscope|exact Hpath].
Qed.

(** Exact SCC blocks depend on admission and root membership rather than list order. *)
Theorem block {V E} (p : Prepared.t V E) source roots target other c :
  (forall x, Scope.admits source x = Scope.admits target x) ->
  (forall x, In x roots <-> In x other) ->
  Scc.block p source roots c -> Scc.block p target other c.
Proof.
  intros Hscope Hroots [Hnonempty [Hnodup [Hreach Hmutual]]].
  split; [exact Hnonempty|]. split; [exact Hnodup|]. split.
  - intros u Hu. apply (proj1 (reachable p source roots target other u Hscope Hroots)).
    exact (Hreach u Hu).
  - intros u v Hu. rewrite (Hmutual u v Hu).
    rewrite (reachable p source roots target other v Hscope Hroots).
    split; intros [Hreachv [[first Hfirst] [last Hlast]]]; split; [exact Hreachv| |exact Hreachv|].
    + split.
      * exists first. exact (path_scope p source target u first v Hscope Hfirst).
      * exists last. exact (path_scope p source target v last u Hscope Hlast).
    + split.
      * exists first. apply (path_scope p target source u first v).
        -- intro x. symmetry. apply Hscope.
        -- exact Hfirst.
      * exists last. apply (path_scope p target source v last u).
        -- intro x. symmetry. apply Hscope.
        -- exact Hlast.
Qed.

(** Entry witnesses transport through the same rooted domain and root membership. *)
Theorem entry {V E} (p : Prepared.t V E) source roots target other c h :
  (forall x, Scope.admits source x = Scope.admits target x) ->
  (forall x, In x roots <-> In x other) ->
  Hier.entry p source roots c h -> Hier.entry p target other c h.
Proof.
  intros Hscope Hroots [Hmember [Hroot|[u [e [Hreach [Houtside Harc]]]]]].
  - split; [exact Hmember|left; now apply Hroots].
  - split; [exact Hmember|right]. exists u, e. split; [|auto].
    apply (proj1 (reachable p source roots target other u Hscope Hroots)). exact Hreach.
Qed.

Local Lemma removed_same source target h c :
  Scope.blocked source = Scope.blocked target ->
  Hier.remove_header source h c = Hier.remove_header target h c.
Proof.
  intro Hblocked. unfold Hier.remove_header. now rewrite Hblocked.
Qed.

Local Lemma blocks {V E} (p : Prepared.t V E) source roots target other f :
  Scope.blocked source = Scope.blocked target ->
  (forall x, Scope.admits source x = Scope.admits target x) ->
  (forall x, In x roots <-> In x other) ->
  Hier.blocks_exact p source roots f -> Hier.blocks_exact p target other f.
Proof.
  intros Hblocked Hscope Hroots Hblocks.
  induction Hblocks as [source roots|source roots v rest Hblock Hself Hrest IH|
    source roots h body rest Hblock Hcyclic Hentry Hbody Hrest IH].
  - constructor.
  - constructor.
    + exact (block p source roots target other [v] Hscope Hroots Hblock).
    + exact Hself.
    + apply IH; assumption.
  - apply Hier.blocks_component.
    + exact (block p source roots target other _ Hscope Hroots Hblock).
    + exact Hcyclic.
    + intros [x Hx]. apply (entry p source roots target other _ h Hscope Hroots).
      apply Hentry. exists x.
      apply (entry p target other source roots _ x).
      * intro v. symmetry. apply Hscope.
      * intro v. symmetry. apply Hroots.
      * exact Hx.
    + rewrite <- (removed_same source target h _ Hblocked). exact Hbody.
    + apply IH; assumption.
Qed.

(** Exact forests transport across equivalent scopes with the same inherited blocked table. *)
Theorem exact {V E} (p : Prepared.t V E) source roots target other f :
  Scope.blocked source = Scope.blocked target ->
  (forall x, Scope.admits source x = Scope.admits target x) ->
  (forall x, In x roots <-> In x other) ->
  Hier.exact p source roots f -> Hier.exact p target other f.
Proof.
  intros Hblocked Hscope Hroots Hexact.
  destruct Hexact as [source roots f Hnodup Hcoverage Hblocks Horder].
  constructor.
  - exact Hnodup.
  - intro v. rewrite Hcoverage. apply reachable; assumption.
  - exact (blocks p source roots target other f Hblocked Hscope Hroots Hblocks).
  - exact Horder.
Qed.

Local Lemma member_tests first last v :
  (In v first <-> In v last) ->
  FinSet.mem positive_encoding v (FinSet.of_list positive_encoding first) =
    FinSet.mem positive_encoding v (FinSet.of_list positive_encoding last).
Proof.
  intro Hmembers. rewrite !FinSet.mem_of_list.
  destruct (existsb (eqb positive_encoding v) first) eqn:Hfirst;
    destruct (existsb (eqb positive_encoding v) last) eqn:Hlast; try reflexivity.
  - apply TarjanStateFacts.member_test in Hfirst.
    apply Hmembers in Hfirst. apply TarjanStateFacts.member_test in Hfirst. congruence.
  - apply TarjanStateFacts.member_test in Hlast.
    apply Hmembers in Hlast. apply TarjanStateFacts.member_test in Hlast. congruence.
Qed.

(** Runtime child restriction agrees with header deletion for every body membership presentation. *)
Theorem child_admits scope h body members v :
  (forall x, In x body <-> In x members) ->
  Scope.admits (HierRun.child_scope scope h body) v =
    Scope.admits (Hier.remove_header scope h (h :: members)) v.
Proof.
  intro Hmembers.
  rewrite !Scope.admits_equation, HierRun.child_scope_equation.
  unfold Hier.remove_header. cbn [Scope.blocked Scope.within].
  rewrite !FinSet.mem_add_raw.
  rewrite (member_tests body members v (Hmembers v)).
  rewrite !FinSet.mem_of_list. cbn [existsb].
  destruct (eqb positive_encoding v h); reflexivity.
Qed.

End HierTransport.
