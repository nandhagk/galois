(** * Scoped flattening and malformed endpoint controls

    Endpoint closure is a real duty of the hierarchy-to-WTO theorem.
    For example, a raw record may number an unlisted target that no scoped path can enter.
    Builds on: GraphHierExact and GraphFixtures. *)

From Stdlib Require Import List Bool PArith.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphModel GraphPrepared GraphVisitor GraphSearchSpec
  GraphSccSpec GraphHierSpec GraphHierExact GraphFixtures.
Import List.ListNotations.
Open Scope positive_scope.

Example corrected_projection_client {V E} (p : Prepared.t V E) scope roots f :
  graph_wf (Prepared.graph p) -> Hier.exact p scope roots f ->
  Wto.valid_within p scope roots (Wto.of_forest f).
Proof.
  apply HierExact.exact_wto_valid.
Qed.

Example ready_projection_client {V E} (p : Prepared.t V E) scope roots f :
  Prepared.ready p -> Hier.exact p scope roots f ->
  Wto.valid_within p scope roots (Wto.of_forest f).
Proof.
  apply HierExact.exact_wto_valid_ready.
Qed.

Definition raw_graph := Fixtures.graph [1%nat] [1%nat] [(1%nat, 2%nat)].
Definition numbered := Fixtures.prepare [1%nat] [1%nat; 2%nat] [(1%nat, 2%nat)].
Definition raw :=
  Prepared.Make raw_graph nat_encoding (Prepared.names numbered)
    Map.empty Map.empty [1] 1.
Definition scope := Scope.Make FinSet.empty None.
Definition singleton := Hier.Cons (Hier.Vertex 1) Hier.Nil.

Local Lemma raw_valid v : Prepared.valid_id raw v -> v = 1.
Proof.
  intros [n [Hn Hid]]. destruct Hn as [<-|Hfalse]; [|contradiction].
  vm_compute in Hid. now inversion Hid.
Qed.

Local Lemma raw_arc u e v : Prepared.arc raw u e v -> u = 1 /\ v = 2.
Proof.
  intros [a [b [Ha [Hu [Hv [Hsource [Htarget He]]]]]]].
  destruct Ha as [<-|Hfalse]; [|contradiction].
  vm_compute in Hu. inversion Hu; subst u.
  vm_compute in He. destruct He as [<-|Hfalse]; [|contradiction].
  vm_compute in Htarget. subst b. vm_compute in Hv.
  inversion Hv. auto.
Qed.

Local Lemma raw_path u es v :
  Search.scoped_path raw scope u es v -> u = 1 /\ v = 1.
Proof.
  intro Hpath. induction Hpath as [v Hv Ha|u e v es z Hu Ha Harc Htail IH].
  - split; now apply raw_valid.
  - destruct (raw_arc u e v Harc) as [_ Hv]. destruct IH as [Hv' _]. congruence.
Qed.

Local Lemma raw_refl : Search.scoped_path raw scope 1 [] 1.
Proof.
  constructor.
  - exists 1%nat. split; [now left|vm_compute; reflexivity].
  - vm_compute. reflexivity.
Qed.

Local Lemma raw_reachable v : Search.scoped_reachable raw scope [1] v <-> v = 1.
Proof.
  split.
  - intros [r [es [Hr Hpath]]]. exact (proj2 (raw_path r es v Hpath)).
  - intros ->. exists 1, []. split; [now left|exact raw_refl].
Qed.

Local Lemma raw_block : Scc.block raw scope [1] [1].
Proof.
  split; [discriminate|]. split.
  - constructor; [intro Hfalse; contradiction|constructor].
  - split.
    + intros u [<-|Hfalse]; [apply raw_reachable; reflexivity|contradiction].
    + intros u v [<-|Hfalse]; [|contradiction].
      split.
      * intros [<-|Hfalse]; [|contradiction].
        split; [apply raw_reachable; reflexivity|].
        split; exists []; exact raw_refl.
      * intros [Hv _]. apply raw_reachable in Hv. subst v. now left.
Qed.

Example malformed_singleton_exact : Hier.exact raw scope [1] singleton.
Proof.
  constructor.
  - constructor; [intro Hfalse; contradiction|constructor].
  - intro v. rewrite raw_reachable. cbn [singleton Hier.members Hier.members_tree app In].
    intuition congruence.
  - constructor.
    + exact raw_block.
    + intros e Harc. destruct (raw_arc 1 e 1 Harc). discriminate.
    + constructor.
  - intros u e v Harc Hu Hv.
    cbn [singleton Hier.members Hier.members_tree app] in Hu, Hv.
    destruct Hu as [<-|Hfalseu], Hv as [<-|Hfalsev]; try contradiction.
    destruct (raw_arc 1 e 1 Harc). discriminate.
Qed.

Example malformed_singleton_not_valid :
  ~ Wto.valid_within raw scope [1] (Wto.of_forest singleton).
Proof.
  intro Hvalid.
  assert (Harc : Prepared.arc raw 1 (1%nat, 2%nat) 2).
  { exists 1%nat, 2%nat. repeat split; vm_compute; auto. }
  destruct (Wto.edges _ _ _ _ Hvalid 1 (1%nat, 2%nat) 2 Harc
    ltac:(vm_compute; auto) ltac:(vm_compute; reflexivity))
    as [Hbefore|[stack [Hrow Hmember]]].
  - destruct Hbefore as [first [middle [last Hsplit]]].
    assert (Hin : In 2 (Wto.order (Wto.of_forest singleton))).
    { rewrite Hsplit. apply in_or_app. right. right.
      apply in_or_app. right. now left. }
    vm_compute in Hin. intuition discriminate.
  - vm_compute in Hrow. destruct Hrow as [Heq|Hfalse]; [|contradiction].
    inversion Heq; subst stack. contradiction.
Qed.
