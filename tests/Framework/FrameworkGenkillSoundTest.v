(** * Two-variable semantic clients

    A program writes x to true and emits y on every edge.
    For example, different initial x values have the same behaviour when y agrees.
    Builds on: FrameworkGenkillSound and FrameworkGenkillLeastTest. *)

From Stdlib Require Import List Bool Arith PArith.
From Galois.Base Require Import BaseEncoding BaseSet.
From Galois.Lattice Require Import LatticeCore LatticeSet LatticeConcrete.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramSemantics ProgramSteps ProgramLink ProgramRuns.
From Galois.Fixpoint Require Import FixpointSystem FixpointAnalysis FixpointCheck.
From Galois.Framework Require Import FrameworkDense FrameworkBitvector FrameworkGenkillSound.
From Galois.Tests.Framework Require Import FrameworkDenseTest FrameworkGenkillLeastTest.
Import List.ListNotations.
Import GenkillSound.

Module TwoVariables.

Record state := St {
  pc : nat;
  x : bool;
  y : bool
}.

Definition get s (u : bool) := if u then y s else x s.

Definition taken (c : Cfg.t nat nat) s l t e :=
  pc s = Graph.source (Cfg.graph c) e /\
  In e (Graph.out (Cfg.graph c) (pc s)) /\
  t = St (Graph.target (Cfg.graph c) e) true (y s) /\ l = [y s].

Definition m c : semantics state bool :=
  Semantics (fun s => In (pc s) (Graph.entries (Cfg.graph c)) /\ y s = false)
    (fun s l t => exists e, taken c s l t e).

Definition lk c : Link.t state bool nat nat :=
  Link.Make pc (taken c) (fun _ _ _ => False).

Definition en (c : Cfg.t nat nat) : endings state :=
  Endings (fun s => Graph.out (Cfg.graph c) (pc s) = []) (fun _ => False) (fun _ => False).

Lemma link_ok c : graph_wf (Cfg.graph c) -> link_laws (m c) (Cfg.graph c) (lk c).
Proof.
  intro Hwf; constructor.
  - exact Hwf.
  - intros s [Hentry _]; exact Hentry.
  - intros s l t Hr [e He]; right; exists e; exact He.
  - intros e s l t Hr Hstep [Hsource [Hout [-> Hlabel]]]; split; [exact Hout|reflexivity].
  - intros s l t Hr Hstep Hbad; contradiction.
Qed.

(** Agreement permits either input y value and keeps x unconstrained. *)
Definition read_m c : semantics state bool :=
  Semantics (fun s => In (pc s) (Graph.entries (Cfg.graph c))) (step (m c)).

Lemma read_link_ok c : graph_wf (Cfg.graph c) -> link_laws (read_m c) (Cfg.graph c) (lk c).
Proof.
  intro Hwf; constructor.
  - exact Hwf.
  - intros s Hentry; exact Hentry.
  - intros s l t Hr [e He]; right; exists e; exact He.
  - intros e s l t Hr Hstep [Hsource [Hout [-> Hlabel]]]; split; [exact Hout|reflexivity].
  - intros s l t Hr Hstep Hbad; contradiction.
Qed.

Definition agree_problem (c : Cfg.t nat nat) :=
  Bitvector.of_pure c bool_encoding [false; true] Backward
    (fun _ => [true]) (fun _ => [false]) (fun _ => Some []).

Lemma agree_laws c : bv_agree_laws (read_m c) (en c) (agree_problem c) (lk c) get.
Proof.
  constructor.
  - intros s l t Hbad; contradiction.
  - intros e u s l t Hr Hstep [_ [_ [-> _]]] Hkill.
    destruct u; [reflexivity|exfalso; apply Hkill; left; reflexivity].
  - intros t e s l s' Hr Hstep Ht Hpoint [Hsource [Hout [-> ->]]] Hinputs.
    change (pc t = pc s) in Hpoint.
    assert (Hy : y s = y t) by (apply (Hinputs true); left; reflexivity).
    exists (St (Graph.target (Cfg.graph c) e) true (y t)); split.
    + exists e; unfold taken; cbn; rewrite <- Hy; repeat split; congruence.
    + split.
      * unfold taken; cbn; rewrite <- Hy; repeat split; congruence.
      * intros u [<-|Hbad]; [reflexivity|contradiction].
  - intros s t Hr Ht Hpoint Hexit; change (pc t = pc s) in Hpoint.
    cbn [en final trapped stopped]; rewrite Hpoint; tauto.
Qed.

Definition live_sigma (_ : nat) := set_of_list bool_encoding [true].

Lemma agreement_client c b :
  encoding_laws (Cfg.node_enc c) -> encoding_laws (Cfg.edge_enc c) ->
  graph_wf (Cfg.graph c) -> In 0 (Graph.entries (Cfg.graph c)) ->
  post_solution (Analysis.lat (Bitvector.may_analysis (agree_problem c)))
    (Analysis.system (Bitvector.may_analysis (agree_problem c))) live_sigma ->
  same_behaviour (read_m c) (en c) (St 0 false b) (read_m c) (en c) (St 0 true b).
Proof.
  intros HN HE Hwf Hentry Hpost.
  eapply (backward_may_sound (read_m c) (en c) (agree_problem c) (lk c) get live_sigma).
  - exact HN.
  - exact HE.
  - exact bool_encoding_laws.
  - reflexivity.
  - apply read_link_ok; exact Hwf.
  - apply agree_laws.
  - exact Hpost.
  - exact Hentry.
  - exact Hentry.
  - reflexivity.
  - intros u Hu; apply (member_list _ bool_encoding_laws) in Hu.
    destruct Hu as [<-|Hbad]; [reflexivity|contradiction].
Qed.

Example agreement_diamond :
  same_behaviour (read_m diamond) (en diamond) (St 0 false false)
    (read_m diamond) (en diamond) (St 0 true false).
Proof.
  apply agreement_client; try exact nat_encoding_laws;
    [exact diamond_wf|vm_compute; tauto|].
  apply check_post_sound; vm_compute; reflexivity.
Qed.

Example agreement_loop :
  same_behaviour (read_m loop) (en loop) (St 0 false true)
    (read_m loop) (en loop) (St 0 true true).
Proof.
  apply agreement_client; try exact nat_encoding_laws;
    [exact loop_wf|vm_compute; tauto|].
  apply check_post_sound; vm_compute; reflexivity.
Qed.

Example agreement_negative :
  check_post (Analysis.lat (Bitvector.may_analysis (agree_problem diamond)))
    (Analysis.system (Bitvector.may_analysis (agree_problem diamond)))
    (fun _ => set_empty bool_encoding) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example agreement_boundary :
  forall u, member (set_empty bool_encoding) u ->
    get (St 3 false false) u = get (St 3 true true) u.
Proof.
  intros [] Hu; vm_compute in Hu; discriminate.
Qed.

Example input_changes_observation :
  step (read_m diamond) (St 0 false true) [true] (St 1 true true) /\
    ~ taken diamond (St 0 false true) [false] (St 1 true true) 0.
Proof.
  split; [exists 0; vm_compute; tauto|].
  intros [_ [_ [_ Hlabel]]]; discriminate.
Qed.

Definition inv_problem (c : Cfg.t nat nat) :=
  Bitvector.of_pure c bool_encoding [false; true] Forward
    (fun _ => [false]) (fun _ => [false]) (fun _ => Some [true]).

Definition holds (u : bool) s := if u then y s = false else x s = true.

Lemma inv_laws c : bv_inv_laws (m c) (inv_problem c) (lk c) holds.
Proof.
  constructor.
  - intros n Hn; exists [true]; reflexivity.
  - intros s xs u [_ Hy] Hb Hu; inversion Hb; subst xs.
    destruct Hu as [<-|Hbad]; [exact Hy|contradiction].
  - intros e u s l t Hr Hstep [_ [_ [-> _]]] [<-|Hbad]; [reflexivity|contradiction].
  - intros e u s l t Hr Hstep [_ [_ [-> _]]] Hkill Hu.
    destruct u; [exact Hu|exfalso; apply Hkill; left; reflexivity].
  - intros u s l t Hr Hstep Hbad; contradiction.
Qed.

Definition inv_sigma n :=
  Only (set_of_list bool_encoding (if Nat.eqb n 0 then [true] else [false; true])).

Lemma invariant_client c :
  encoding_laws (Cfg.node_enc c) -> encoding_laws (Cfg.edge_enc c) ->
  graph_wf (Cfg.graph c) ->
  post_solution (Analysis.lat (Bitvector.must_analysis (inv_problem c)))
    (Analysis.system (Bitvector.must_analysis (inv_problem c))) inv_sigma ->
  forall s, reachable_state (m c) s ->
    gamma (must_gamma bool_encoding holds) (inv_sigma (pc s)) s.
Proof.
  intros HN HE Hwf Hpost.
  eapply (forward_must_sound (m c) (inv_problem c) (lk c) holds inv_sigma);
    try exact HN; try exact HE; try exact bool_encoding_laws; try reflexivity.
  - apply link_ok; exact Hwf.
  - apply inv_laws.
  - exact Hpost.
Qed.

Example invariant_diamond :
  forall s, reachable_state (m diamond) s ->
    gamma (must_gamma bool_encoding holds) (inv_sigma (pc s)) s.
Proof.
  apply invariant_client; try exact nat_encoding_laws; [exact diamond_wf|].
  apply check_post_sound; vm_compute; reflexivity.
Qed.

Example invariant_loop :
  forall s, reachable_state (m loop) s ->
    gamma (must_gamma bool_encoding holds) (inv_sigma (pc s)) s.
Proof.
  apply invariant_client; try exact nat_encoding_laws; [exact loop_wf|].
  apply check_post_sound; vm_compute; reflexivity.
Qed.

Example invariant_negative :
  check_post (Analysis.lat (Bitvector.must_analysis (inv_problem diamond)))
    (Analysis.system (Bitvector.must_analysis (inv_problem diamond)))
    (fun _ => Only (set_of_list bool_encoding [false; true])) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example invariant_entry : holds true (St 0 false false) /\ ~ holds false (St 0 false false).
Proof.
  vm_compute; split; [reflexivity|discriminate].
Qed.

Definition past (_ : state) (es : list nat) (_ : state) u :=
  u = true \/ (u = false /\ es <> []).

Lemma cover_laws c : bv_cover_laws (m c) (inv_problem c) (lk c) past.
Proof.
  constructor.
  - intros n Hn; exists [true]; reflexivity.
  - intros s xs u Hi Hb [->|[_ Hbad]]; [inversion Hb; left; reflexivity|contradiction].
  - intros e s0 es u s l t Hr Hstep Hi Hrun Htaken [->|[-> Hnonempty]].
    + left; split; [left; reflexivity|intros [Hbad|Hbad]; [discriminate|contradiction]].
    + right; left; reflexivity.
  - intros s0 es u s l t Hr Hstep Hi Hrun Hbad; contradiction.
Qed.

Definition cover_sigma (_ : nat) := set_of_list bool_encoding [false; true].

Lemma cover_client c :
  encoding_laws (Cfg.node_enc c) -> encoding_laws (Cfg.edge_enc c) ->
  graph_wf (Cfg.graph c) ->
  post_solution (Analysis.lat (Bitvector.may_analysis (inv_problem c)))
    (Analysis.system (Bitvector.may_analysis (inv_problem c))) cover_sigma ->
  forall s0 es s u, initial (m c) s0 -> run_edges (m c) (lk c) s0 es s ->
    past s0 es s u -> member (cover_sigma (pc s)) u.
Proof.
  intros HN HE Hwf Hpost.
  eapply (forward_may_cover (m c) (inv_problem c) (lk c) past cover_sigma);
    try exact HN; try exact HE; try exact bool_encoding_laws; try reflexivity.
  - apply link_ok; exact Hwf.
  - apply cover_laws.
  - exact Hpost.
Qed.

Example cover_diamond :
  forall s0 es s u, initial (m diamond) s0 -> run_edges (m diamond) (lk diamond) s0 es s ->
    past s0 es s u -> member (cover_sigma (pc s)) u.
Proof.
  apply cover_client; try exact nat_encoding_laws; [exact diamond_wf|].
  apply check_post_sound; vm_compute; reflexivity.
Qed.

Example cover_loop :
  forall s0 es s u, initial (m loop) s0 -> run_edges (m loop) (lk loop) s0 es s ->
    past s0 es s u -> member (cover_sigma (pc s)) u.
Proof.
  apply cover_client; try exact nat_encoding_laws; [exact loop_wf|].
  apply check_post_sound; vm_compute; reflexivity.
Qed.

Example cover_negative : ~ past (St 0 false false) [] (St 0 false false) false.
Proof.
  vm_compute; intuition discriminate.
Qed.

Example cover_boundary : past (St 0 false false) [] (St 0 false false) true.
Proof.
  left; reflexivity.
Qed.

Definition witness_problem (c : Cfg.t nat nat) exit :=
  Bitvector.of_pure c bool_encoding [false; true] Backward
    (fun _ => [true]) (fun _ => [false])
    (fun n => if Nat.eqb n exit then Some [] else None).

Definition future (_ : state) (es : list nat) (_ : state) u := u = true /\ es <> [].

Lemma witness_laws c exit :
  bv_witness_laws (m c) (witness_problem c exit) (lk c) (fun s => pc s = exit) future.
Proof.
  constructor.
  - intros t Hr HQ; exists []; change (pc t = exit) in HQ.
    change ((if Nat.eqb (pc t) exit then Some (@nil bool) else None) = Some []).
    rewrite HQ, Nat.eqb_refl.
    reflexivity.
  - intros t xs u Hr HQ Hb Hu; change (pc t = exit) in HQ.
    change ((if Nat.eqb (pc t) exit then Some [] else None) = Some xs) in Hb.
    rewrite HQ, Nat.eqb_refl in Hb; inversion Hb; subst xs; contradiction.
  - intros e es t u s l s' Hr Hstep Hrun HQ Htaken [<-|Hbad];
      [split; [reflexivity|discriminate]|contradiction].
  - intros e es t u s l s' Hr Hstep Hrun HQ Htaken Hkill [Hu Hnonempty].
    split; [exact Hu|discriminate].
  - intros es t u s l s' Hr Hstep Hrun HQ Hbad; contradiction.
Qed.

Definition busy_sigma exit n :=
  Only (set_of_list bool_encoding (if Nat.eqb n exit then [] else [true])).

Lemma witness_client c exit :
  encoding_laws (Cfg.node_enc c) -> encoding_laws (Cfg.edge_enc c) ->
  graph_wf (Cfg.graph c) ->
  post_solution (Analysis.lat (Bitvector.must_analysis (witness_problem c exit)))
    (Analysis.system (Bitvector.must_analysis (witness_problem c exit))) (busy_sigma exit) ->
  forall s es t u, reachable_state (m c) s -> run_edges (m c) (lk c) s es t ->
    pc t = exit -> must_member (busy_sigma exit (pc s)) u -> future s es t u.
Proof.
  intros HN HE Hwf Hpost.
  eapply (backward_must_witness (m c) (witness_problem c exit) (lk c)
    (fun s => pc s = exit) future (busy_sigma exit));
    try exact HN; try exact HE; try exact bool_encoding_laws; try reflexivity.
  - apply link_ok; exact Hwf.
  - apply witness_laws.
  - exact Hpost.
Qed.

Example witness_diamond :
  forall s es t u, reachable_state (m diamond) s -> run_edges (m diamond) (lk diamond) s es t ->
    pc t = 3 -> must_member (busy_sigma 3 (pc s)) u -> future s es t u.
Proof.
  apply witness_client; try exact nat_encoding_laws; [exact diamond_wf|].
  apply check_post_sound; vm_compute; reflexivity.
Qed.

Example witness_loop :
  forall s es t u, reachable_state (m loop) s -> run_edges (m loop) (lk loop) s es t ->
    pc t = 2 -> must_member (busy_sigma 2 (pc s)) u -> future s es t u.
Proof.
  apply witness_client; try exact nat_encoding_laws; [exact loop_wf|].
  apply check_post_sound; vm_compute; reflexivity.
Qed.

Example witness_negative :
  check_post (Analysis.lat (Bitvector.must_analysis (witness_problem diamond 3)))
    (Analysis.system (Bitvector.must_analysis (witness_problem diamond 3)))
    (fun _ => Only (set_of_list bool_encoding [true])) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example witness_empty_terminal : ~ must_member (busy_sigma 3 3) true.
Proof.
  vm_compute; discriminate.
Qed.

Definition history_problem (c : Cfg.t nat nat) :=
  Bitvector.of_pure c bool_encoding [false; true] Forward
    (fun _ => [true]) (fun _ => [false]) (fun _ => Some []).

Definition computed c s0 es s u :=
  exists pre mid e post, es = pre ++ e :: post /\
    run_edges (m c) (lk c) s0 pre mid /\
    run_edges (m c) (lk c) mid (e :: post) s /\
    u = true /\ get s u = get mid u.

Lemma computed_gen c e s0 es s l t u :
  run_edges (m c) (lk c) s0 es s -> taken c s l t e ->
  In u [true] -> computed c s0 (es ++ [e]) t u.
Proof.
  intros Hrun Htaken [<-|Hbad]; [|contradiction].
  exists es, s, e, []; split; [reflexivity|]; split; [exact Hrun|]; split.
  - econstructor; [exists e; exact Htaken|exact Htaken|constructor].
  - split; [reflexivity|]; destruct Htaken as [_ [_ [-> _]]]; reflexivity.
Qed.

Lemma computed_frame c e s0 es s l t u :
  taken c s l t e -> computed c s0 es s u -> computed c s0 (es ++ [e]) t u.
Proof.
  intros Htaken [pre [mid [d [post [Hes [Hpre [Hpost [-> Hvalue]]]]]]]].
  exists pre, mid, d, (post ++ [e]); split.
  - rewrite Hes, <- app_assoc; reflexivity.
  - split; [exact Hpre|]; split.
    + change (run_edges (m c) (lk c) mid ((d :: post) ++ [e]) t).
      eapply run_edges_app; [exact Hpost|].
      econstructor; [exists e; exact Htaken|exact Htaken|constructor].
    + split; [reflexivity|].
      destruct Htaken as [_ [_ [-> _]]]; exact Hvalue.
Qed.

Lemma history_laws c : bv_history_laws (m c) (history_problem c) (lk c) (computed c).
Proof.
  constructor.
  - intros n Hn; exists []; reflexivity.
  - intros s xs u Hi Hb Hu; inversion Hb; subst xs; contradiction.
  - intros e s0 es u s l t Hr Hstep Hi Hrun Htaken Hu.
    exact (computed_gen c e s0 es s l t u Hrun Htaken Hu).
  - intros e s0 es u s l t Hr Hstep Hi Hrun Htaken Hkill Hcomputed.
    exact (computed_frame c e s0 es s l t u Htaken Hcomputed).
  - intros s0 es u s l t Hr Hstep Hi Hrun Hbad; contradiction.
Qed.

Definition history_sigma n :=
  Only (set_of_list bool_encoding (if Nat.eqb n 0 then [] else [true])).

Lemma history_client c :
  encoding_laws (Cfg.node_enc c) -> encoding_laws (Cfg.edge_enc c) ->
  graph_wf (Cfg.graph c) ->
  post_solution (Analysis.lat (Bitvector.must_analysis (history_problem c)))
    (Analysis.system (Bitvector.must_analysis (history_problem c))) history_sigma ->
  forall s0 es s u, initial (m c) s0 -> run_edges (m c) (lk c) s0 es s ->
    must_member (history_sigma (pc s)) u -> computed c s0 es s u.
Proof.
  intros HN HE Hwf Hpost.
  eapply (forward_must_history (m c) (history_problem c) (lk c) (computed c) history_sigma);
    try exact HN; try exact HE; try exact bool_encoding_laws; try reflexivity.
  - apply link_ok; exact Hwf.
  - apply history_laws.
  - exact Hpost.
Qed.

Example availability_diamond :
  forall s0 es s u, initial (m diamond) s0 -> run_edges (m diamond) (lk diamond) s0 es s ->
    must_member (history_sigma (pc s)) u -> computed diamond s0 es s u.
Proof.
  apply history_client; try exact nat_encoding_laws; [exact diamond_wf|].
  apply check_post_sound; vm_compute; reflexivity.
Qed.

Example availability_loop :
  forall s0 es s u, initial (m loop) s0 -> run_edges (m loop) (lk loop) s0 es s ->
    must_member (history_sigma (pc s)) u -> computed loop s0 es s u.
Proof.
  apply history_client; try exact nat_encoding_laws; [exact loop_wf|].
  apply check_post_sound; vm_compute; reflexivity.
Qed.

Example actual_diamond_step :
  step (m diamond) (St 0 false false) [false] (St 1 true false).
Proof.
  exists 0; vm_compute; tauto.
Qed.

Example actual_loop_history :
  run_edges (m loop) (lk loop) (St 0 false false) [0; 1; 2] (St 2 true false).
Proof.
  eapply run_take with (s' := St 1 true false) (l := [false]).
  - exists 0; vm_compute; tauto.
  - vm_compute; tauto.
  - eapply run_take with (s' := St 1 true false) (l := [false]).
    + exists 1; vm_compute; tauto.
    + vm_compute; tauto.
    + eapply run_take with (s' := St 2 true false) (l := [false]).
      * exists 2; vm_compute; tauto.
      * vm_compute; tauto.
      * constructor.
Qed.

Example actual_loop_computation :
  computed loop (St 0 false false) [0; 1; 2] (St 2 true false) true.
Proof.
  apply availability_loop.
  - split; [vm_compute; tauto|reflexivity].
  - exact actual_loop_history.
  - vm_compute; reflexivity.
Qed.

Example actual_loop_witness :
  future (St 0 false false) [0; 1; 2] (St 2 true false) true.
Proof.
  eapply witness_loop.
  - exists (St 0 false false), []; split; [split; [vm_compute; tauto|reflexivity]|constructor].
  - exact actual_loop_history.
  - reflexivity.
  - vm_compute; reflexivity.
Qed.

Example loop_semantic_instances_run_without_laws :
  option_map (map (fun a => FinSet.elements (set_raw a)))
    (observe (Bitvector.may_analysis (agree_problem loop)) 16%positive [0; 1; 2]) =
      Some [[true]; [true]; []] /\
  option_map (map (fun a => match a with
    | All => None
    | Only a => Some (FinSet.elements (set_raw a))
    end))
    (observe (Bitvector.must_analysis (inv_problem loop)) 16%positive [0; 1; 2]) =
      Some [Some [true]; Some [true; false]; Some [true; false]].
Proof.
  vm_compute; split; reflexivity.
Qed.

End TwoVariables.
