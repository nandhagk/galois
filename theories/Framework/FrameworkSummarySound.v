(** * Sound summaries through suspended callers

    Post-solutions cover local steps and lift that coverage through every active caller.
    For example, a caller's summary covers a step inside a recursive callee.
    Builds on: FrameworkSummary, ProgramCalls and ProgramSteps. *)

From Stdlib Require Import List Bool Arith Lia.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap.
From Galois.Lattice Require Import LatticeCore.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramSemantics ProgramSteps ProgramCalls ProgramIcfg.
From Galois.Fixpoint Require Import FixpointQuery FixpointSystem FixpointLeast FixpointAnalysis.
From Galois.Framework Require Import FrameworkUtil FrameworkRows FrameworkIfds FrameworkStack
  FrameworkSummary.
Import List.ListNotations Cost.Notations.

Module SummarySound.

(** Coverage relates a summary to an event-labelled concrete transition. *)
Record step_cover (S O A : Type) := StepCover {
  step_covers : A -> S -> list O -> S -> Prop
}.
Arguments StepCover {S O A}.
Arguments step_covers {S O A}.

(** Local effects include external activity and calls lift coverage through suspended frames. *)
Record summary_laws {S O F P A} (m : semantics S O) (C : Calls.t F P)
    (cl : CallsLink.t S F P) (sp : Summary.spec F P A) (sc : step_cover S O A) : Prop := {
  covers_monotone : forall a b, leb (Summary.lat sp) a b = true ->
    on_steps m (fun s l t => step_covers sc a s l t -> step_covers sc b s l t);
  local_covers : on_steps m
    (fun s l t => step_covers sc (Summary.local sp (CallsLink.here cl s)) s l t);
  call_covers : forall p g a, on_steps m (fun s l t =>
    In (Calls.caller_of C p, p) (CallsLink.frames cl s) ->
    step_covers sc a s l t -> step_covers sc (Summary.via_call sp p g a) s l t)
}.
Arguments covers_monotone {S O F P A m C cl sp sc}.
Arguments local_covers {S O F P A m C cl sp sc}.
Arguments call_covers {S O F P A m C cl sp sc}.

Local Lemma lookup_fold {X V} (E : encoding X) (HE : encoding_laws E)
    (f : X -> V) x xs old :
  old = Some (f x) \/ In x xs ->
  fold_left (fun acc kv => if eqb E x (fst kv) then Some (snd kv) else acc)
    (map (fun y => (y, f y)) xs) old = Some (f x).
Proof.
  revert old; induction xs as [|y xs IH]; intros old Hin;
    cbn -[eqb] in Hin |- *.
  - destruct Hin as [->|[]]; reflexivity.
  - destruct (eqb E x y) eqn:Hxy.
    + apply (eqb_true_iff E HE) in Hxy; subst y; apply IH; left; reflexivity.
    + apply IH; destruct Hin as [Heq|[Heq|Hin]]; auto.
      subst y; rewrite (proj2 (eqb_true_iff E HE x x) eq_refl) in Hxy; discriminate.
Qed.

(** Preparing a table from a key-indexed function retains its value even with duplicate keys. *)
Theorem table_lookup {X V} (E : encoding X) (HE : encoding_laws E)
    (f : X -> V) xs x :
  In x xs -> Map.get E x (Map.of_list E (map (fun y => (y, f y)) xs)) = Some (f x).
Proof.
  intro Hin; rewrite Map.of_list_get; apply (lookup_fold E HE); now right.
Qed.

(** Absent keys remain absent in a prepared table with lawful encodings. *)
Theorem table_absent {X V} (E : encoding X) (HE : encoding_laws E)
    (f : X -> V) xs x :
  ~ In x xs -> Map.get E x (Map.of_list E (map (fun y => (y, f y)) xs)) = None.
Proof.
  rewrite Map.of_list_get; intro Hnot.
  assert (Hall : forall y, In y xs -> eqb E x y = false).
  { intros y Hy; destruct (eqb E x y) eqn:Heq; [|reflexivity].
    apply (eqb_true_iff E HE) in Heq; subst y; contradiction. }
  induction xs as [|y xs IH]; [reflexivity|].
  cbn -[eqb]; rewrite (Hall y (or_introl eq_refl)); apply IH.
  - intros Hin; apply Hnot; now right.
  - intros z Hz; apply Hall; now right.
Qed.

(** Row enumeration retains each local row and every resolved call occurrence. *)
Theorem rows_equation {F P} (C : Calls.t F P) :
  Cost.value (Summary.rows_c C) =
    map Summary.SLocal (Calls.functions C) ++
    flat_map (fun f => flat_map (fun p => map (Summary.SCall p) (Calls.resolve C p))
      (Calls.sites_of C f)) (Calls.functions C).
Proof.
  unfold Summary.rows_c; autorewrite with galois_cost.
  rewrite fw_flat_map_value; f_equal.
  apply flat_map_ext; intro f; autorewrite with galois_cost.
  rewrite fw_flat_map_value; apply flat_map_ext; intro p.
  autorewrite with galois_cost; reflexivity.
Qed.

Local Lemma local_row {F P} (C : Calls.t F P) f :
  In f (Calls.functions C) -> In (Summary.SLocal f) (Cost.value (Summary.rows_c C)).
Proof.
  intro Hin; rewrite rows_equation; apply in_or_app; left; apply in_map; exact Hin.
Qed.

Local Lemma call_row {F P} (C : Calls.t F P) f p g :
  In f (Calls.functions C) -> In p (Calls.sites_of C f) -> In g (Calls.resolve C p) ->
  In (Summary.SCall p g) (Cost.value (Summary.rows_c C)).
Proof.
  intros Hf Hp Hg; rewrite rows_equation; apply in_or_app; right.
  apply in_flat_map; exists f; split; [exact Hf|].
  apply in_flat_map; exists p; split; [exact Hp|apply in_map; exact Hg].
Qed.

(** Prepared rows expose their target, evaluation and absence of side contributions. *)
Theorem row_spec {F P A} (C : Calls.t F P) (sp : Summary.spec F P A) r sigma :
  encoding_laws (Calls.fn_enc C) -> encoding_laws (Calls.site_enc C) ->
  In r (Cost.value (Summary.rows_c C)) ->
  let sys := Analysis.system (summary_analysis C sp) in
  In r (System.constraints sys) /\
  System.target sys r = Rows.target (Cost.value (Summary.get_c C sp r)) /\
  Query.eval (System.rhs sys r) sigma =
    Cost.value (Rows.eval_c (Cost.value (Summary.get_c C sp r))
      (map sigma (Rows.reads (Cost.value (Summary.get_c C sp r))))) /\
  Query.sides (System.rhs sys r) sigma = [].
Proof.
  intros HF HP Hr; unfold summary_analysis, Summary.analysis, Summary.prepare_c.
  autorewrite with galois_cost.
  set (cs := Cost.value (Summary.rows_c C)) in *.
  set (plan := fun r => Cost.value (Summary.get_c C sp r)).
  assert (Hget : forall d, Map.find_or (Summary.row_enc C) d r
    (Map.of_list (Summary.row_enc C) (map (fun row => (row, plan row)) cs)) = plan r).
  { intro d; rewrite Map.find_or_equation, table_lookup; [reflexivity| |exact Hr].
    apply Summary.row_enc_laws; assumption. }
  split; [exact Hr|].
  set (table := Map.of_list (Summary.row_enc C) (map (fun row => (row, plan row)) cs)).
  assert (Hprepared : Cost.value (Summary.prepared_get_c C sp table r) = plan r).
  { destruct r as [f|p g]; apply Hget. }
  change (Rows.target (Cost.value (Summary.prepared_get_c C sp table r)) =
      Rows.target (plan r) /\
    Query.eval (Rows.query (Cost.value (Summary.prepared_get_c C sp table r))) sigma =
      Cost.value (Rows.eval_c (plan r) (map sigma (Rows.reads (plan r)))) /\
    Query.sides (Rows.query (Cost.value (Summary.prepared_get_c C sp table r))) sigma = []).
  rewrite Hprepared; split; [reflexivity|apply (proj2 (Rows.query_spec _ _))].
Qed.

(** A post-solution bounds each listed function's local effect. *)
Theorem local_bound {F P A} (C : Calls.t F P) (sp : Summary.spec F P A) sigma :
  encoding_laws (Calls.fn_enc C) -> encoding_laws (Calls.site_enc C) ->
  post_solution (Summary.lat sp) (Analysis.system (summary_analysis C sp)) sigma ->
  forall f, In f (Calls.functions C) ->
    leb (Summary.lat sp) (Summary.local sp f) (sigma f) = true.
Proof.
  intros HF HP Hpost f Hf.
  destruct (row_spec C sp (Summary.SLocal f) sigma HF HP (local_row C f Hf))
    as [Hr [Ht [Hv Hs]]].
  specialize (Hpost _ Hr); rewrite Ht, Hv in Hpost; exact (proj1 Hpost).
Qed.

(** A post-solution bounds each resolved callee lifted through its call site. *)
Theorem call_bound {F P A} (C : Calls.t F P) (sp : Summary.spec F P A) sigma :
  encoding_laws (Calls.fn_enc C) -> encoding_laws (Calls.site_enc C) ->
  post_solution (Summary.lat sp) (Analysis.system (summary_analysis C sp)) sigma ->
  forall f p g, In f (Calls.functions C) -> In p (Calls.sites_of C f) ->
    In g (Calls.resolve C p) ->
    leb (Summary.lat sp) (Summary.via_call sp p g (sigma g))
      (sigma (Calls.caller_of C p)) = true.
Proof.
  intros HF HP Hpost f p g Hf Hp Hg.
  destruct (row_spec C sp (Summary.SCall p g) sigma HF HP (call_row C f p g Hf Hp Hg))
    as [Hr [Ht [Hv Hs]]].
  specialize (Hpost _ Hr); rewrite Ht, Hv in Hpost; exact (proj1 Hpost).
Qed.

(** Linked frames are an inductive resolver chain from the current callee outwards. *)
Inductive frames_linked {F P} (C : Calls.t F P) : F -> list (F * P) -> Prop :=
  | frames_nil g : frames_linked C g []
  | frames_cons g f p rest :
      Calls.caller_of C p = f ->
      In p (Calls.sites_of C f) ->
      In g (Calls.resolve C p) ->
      frames_linked C f rest ->
      frames_linked C g ((f, p) :: rest).

(** Internal steps, listed pushes and matched returns retain the inductive frame chain. *)
Theorem frames_linked_step {S O F P} (m : semantics S O) (C : Calls.t F P)
    (cl : CallsLink.t S F P) :
  calls_laws m C cl ->
  on_steps m (fun s _ t =>
    frames_linked C (CallsLink.here cl s) (CallsLink.frames cl s) ->
    frames_linked C (CallsLink.here cl t) (CallsLink.frames cl t)).
Proof.
  intros Hcalls s l t Hreach Hstep Hlinked.
  destruct (step_shape Hcalls s l t Hreach Hstep) as
    [[Hhere Hstack]|[[p [Hp [Hg Hstack]]]|[f [p [Hstack Hhere]]]]].
  - rewrite Hhere, Hstack; exact Hlinked.
  - rewrite Hstack; constructor; [eapply sites_caller; eassumption|exact Hp|exact Hg|].
    exact Hlinked.
  - rewrite Hstack in Hlinked; inversion Hlinked; subst; assumption.
Qed.

(** Reachable states have inductively linked suspended frames. *)
Theorem reachable_frames_linked {S O F P} (m : semantics S O) (C : Calls.t F P)
    (cl : CallsLink.t S F P) :
  calls_laws m C cl -> forall s, reachable_state m s ->
    frames_linked C (CallsLink.here cl s) (CallsLink.frames cl s).
Proof.
  intro Hcalls; apply reachable_ind.
  - intros s Hinit; rewrite (proj2 (initial_roots Hcalls s Hinit)); constructor.
  - intros s l t Hreach IH Hstep.
    exact (frames_linked_step m C cl Hcalls s l t Hreach Hstep IH).
Qed.

(** Lifting through linked frames covers the same concrete step at every active caller. *)
Theorem frames_cover {S O F P A} (m : semantics S O) (C : Calls.t F P)
    (cl : CallsLink.t S F P) (sp : Summary.spec F P A) (sc : step_cover S O A) sigma :
  encoding_laws (Calls.fn_enc C) -> encoding_laws (Calls.site_enc C) ->
  summary_laws m C cl sp sc ->
  post_solution (Summary.lat sp) (Analysis.system (summary_analysis C sp)) sigma ->
  forall s l t, reachable_state m s -> step m s l t ->
  forall g stack, frames_linked C g stack -> incl stack (CallsLink.frames cl s) ->
    incl (map fst stack) (Calls.functions C) ->
    step_covers sc (sigma g) s l t ->
    forall f, In f (g :: map fst stack) -> step_covers sc (sigma f) s l t.
Proof.
  intros HF HP Hlaws Hpost s l t Hreach Hstep g stack Hlinked.
  induction Hlinked as [g|g caller p rest Hcaller Hsite Htarget Hlinked IH];
    intros Hstack Hlisted Hcover f Hin.
  - destruct Hin as [<-|[]]; exact Hcover.
  - destruct Hin as [<-|Hin]; [exact Hcover|].
    apply IH with (f := f).
    + intros fr Hfr; apply Hstack; now right.
    + intros h Hh; apply Hlisted; now right.
    + eapply (covers_monotone Hlaws _ _); [|exact Hreach|exact Hstep|].
      * rewrite <- Hcaller; eapply call_bound;
          [exact HF|exact HP|exact Hpost| |exact Hsite|exact Htarget].
        apply Hlisted; left; reflexivity.
      * apply (call_covers Hlaws p g _ s l t Hreach Hstep).
        -- rewrite Hcaller; apply Hstack; left; reflexivity.
        -- exact Hcover.
    + exact Hin.
Qed.

(** Every active function's post-solution covers every step, including callee activity. *)
Theorem sound {S O F P A} (m : semantics S O) (C : Calls.t F P)
    (cl : CallsLink.t S F P) (sp : Summary.spec F P A) (sc : step_cover S O A) sigma :
  encoding_laws (Calls.fn_enc C) -> encoding_laws (Calls.site_enc C) ->
  calls_laws m C cl -> summary_laws m C cl sp sc ->
  post_solution (Summary.lat sp) (Analysis.system (summary_analysis C sp)) sigma ->
  forall s l t f, reachable_state m s -> step m s l t -> In f (Calls.active cl s) ->
    step_covers sc (sigma f) s l t.
Proof.
  intros HF HP Hcalls Hlaws Hpost s l t f Hreach Hstep Hin.
  eapply (frames_cover m C cl sp sc sigma HF HP Hlaws Hpost s l t Hreach Hstep
    (CallsLink.here cl s) (CallsLink.frames cl s)).
  - exact (reachable_frames_linked m C cl Hcalls s Hreach).
  - apply incl_refl.
  - intros g Hg; apply (frames_listed Hcalls s Hreach); now right.
  - eapply (covers_monotone Hlaws _ _); [|exact Hreach|exact Hstep|].
    + apply (local_bound C sp sigma HF HP Hpost).
      apply (frames_listed Hcalls s Hreach); left; reflexivity.
    + exact (local_covers Hlaws s l t Hreach Hstep).
  - exact Hin.
Qed.

(* The prepared-row interface is shared by soundness and leastness clients. *)
(** Summary post-solutions satisfy exactly the local and resolved-call inequalities. *)
Theorem post_solution_iff {F P A} (C : Calls.t F P) (sp : Summary.spec F P A) sigma :
  encoding_laws (Calls.fn_enc C) -> encoding_laws (Calls.site_enc C) ->
  (post_solution (Summary.lat sp) (Analysis.system (summary_analysis C sp)) sigma <->
    (forall f, In f (Calls.functions C) ->
      leb (Summary.lat sp) (Summary.local sp f) (sigma f) = true) /\
    (forall f p g, In f (Calls.functions C) -> In p (Calls.sites_of C f) ->
      In g (Calls.resolve C p) ->
      leb (Summary.lat sp) (Summary.via_call sp p g (sigma g))
        (sigma (Calls.caller_of C p)) = true)).
Proof.
  intros HF HP; split.
  - intro Hpost; split.
    + exact (local_bound C sp sigma HF HP Hpost).
    + exact (call_bound C sp sigma HF HP Hpost).
  - intros [Hlocal Hcall] r Hr.
    assert (Hrows : System.constraints (Analysis.system (summary_analysis C sp)) =
      Cost.value (Summary.rows_c C)).
    { unfold summary_analysis, Summary.analysis, Summary.prepare_c;
        autorewrite with galois_cost; reflexivity. }
    rewrite Hrows in Hr.
    destruct (row_spec C sp r sigma HF HP Hr) as [_ [Ht [Hv Hs]]].
    rewrite Ht, Hv, Hs; split; [|intros x a Hbad; contradiction].
    rewrite rows_equation in Hr; destruct r as [f|p g].
    + apply Hlocal.
      apply in_app_or in Hr; destruct Hr as [Hr|Hr].
      * apply in_map_iff in Hr; destruct Hr as [h [Heq Hh]]; inversion Heq; subst h.
        exact Hh.
      * apply in_flat_map in Hr; destruct Hr as [h [_ Hr]].
        apply in_flat_map in Hr; destruct Hr as [q [_ Hr]].
        apply in_map_iff in Hr; destruct Hr as [g [Heq _]]; discriminate.
    + apply in_app_or in Hr; destruct Hr as [Hr|Hr].
      * apply in_map_iff in Hr; destruct Hr as [h [Heq _]]; discriminate.
      * apply in_flat_map in Hr; destruct Hr as [f [Hf Hr]].
        apply in_flat_map in Hr; destruct Hr as [q [Hq Hr]].
        apply in_map_iff in Hr; destruct Hr as [h [Heq Hh]]; inversion Heq; subst q h.
        exact (Hcall f p g Hf Hq Hh).
Qed.

(** Context rows range over the supplied support, independently of its closure laws. *)
Definition ctx_rows {F P K} (C : Calls.t F P) (cx : Ctx.t F P K) :=
  flat_map (fun k => map (fun r => (r, k)) (Cost.value (Summary.rows_c C)))
    (Ctx.contexts cx).

(** Context-major row membership retains both support and base-row membership. *)
Theorem ctx_row_member {F P K} (C : Calls.t F P) (cx : Ctx.t F P K) r k :
  In (r, k) (ctx_rows C cx) <->
    In k (Ctx.contexts cx) /\ In r (Cost.value (Summary.rows_c C)).
Proof.
  unfold ctx_rows; rewrite in_flat_map; split.
  - intros [c [Hc Hr]]; apply in_map_iff in Hr.
    destruct Hr as [row [Heq Hr]]; inversion Heq; subst c row; auto.
  - intros [Hk Hr]; exists k; split; [exact Hk|].
    apply in_map_iff; exists r; auto.
Qed.

(** Context row observations agree with their compiled plans on the supported inventory. *)
Theorem ctx_row_spec {F P K A} (C : Calls.t F P) (cx : Ctx.t F P K)
    (sp : Summary.spec F P A) rk sigma :
  encoding_laws (Calls.fn_enc C) -> encoding_laws (Calls.site_enc C) ->
  encoding_laws (Ctx.ctx_enc cx) -> In rk (ctx_rows C cx) ->
  let sys := Analysis.system (ctx_summary_analysis C cx sp) in
  In rk (System.constraints sys) /\
  System.target sys rk = Rows.target (Cost.value (Summary.ctx_get_c C cx sp rk)) /\
  Query.eval (System.rhs sys rk) sigma =
    Cost.value (Rows.eval_c (Cost.value (Summary.ctx_get_c C cx sp rk))
      (map sigma (Rows.reads (Cost.value (Summary.ctx_get_c C cx sp rk))))) /\
  Query.sides (System.rhs sys rk) sigma = [].
Proof.
  intros HF HP HK Hr; unfold ctx_summary_analysis, Summary.ctx_analysis.
  assert (Hrows : Cost.value (fw_flat_map_c (fun k =>
    map_c (fun r => Cost.ret (r, k)) (Cost.value (Summary.rows_c C)))
    (Ctx.contexts cx)) = ctx_rows C cx).
  { rewrite fw_flat_map_value; unfold ctx_rows; apply flat_map_ext; intro k.
    rewrite value_map_c; reflexivity. }
  rewrite Hrows; autorewrite with galois_cost.
  set (plan := fun rk => Cost.value (Summary.ctx_get_c C cx sp rk)).
  set (EC := FrameworkKey.pair (Summary.row_enc C) (Ctx.ctx_enc cx)).
  set (table := Map.of_list EC (map (fun rk => (rk, plan rk)) (ctx_rows C cx))).
  assert (HE : encoding_laws EC).
  { apply FrameworkKey.pair_laws; [apply Summary.row_enc_laws; assumption|exact HK]. }
  assert (Hget : forall d, Map.find_or EC d rk table = plan rk).
  { intro d; unfold table; rewrite Map.find_or_equation, (table_lookup EC HE);
      [reflexivity|exact Hr]. }
  split; [exact Hr|].
  destruct rk as [r k].
  set (f := match r with Summary.SLocal f => f | Summary.SCall _ g => g end).
  change (Rows.target (Map.find_or EC (Rows.Make (f, k) []
      (fun _ => Cost.ret (bot (Summary.lat sp)))) (r, k) table) =
      Rows.target (plan (r, k)) /\
    Query.eval (Rows.query (Map.find_or EC (Rows.Make (f, k) []
      (fun _ => Cost.ret (bot (Summary.lat sp)))) (r, k) table)) sigma =
      Cost.value (Rows.eval_c (plan (r, k)) (map sigma (Rows.reads (plan (r, k))))) /\
    Query.sides (Rows.query (Map.find_or EC (Rows.Make (f, k) []
      (fun _ => Cost.ret (bot (Summary.lat sp)))) (r, k) table)) sigma = []).
  rewrite !Hget; split; [reflexivity|apply (proj2 (Rows.query_spec _ _))].
Qed.

(** A supported context's local row bounds its local effect. *)
Theorem ctx_local_bound {F P K A} (C : Calls.t F P) (cx : Ctx.t F P K)
    (sp : Summary.spec F P A) sigma :
  encoding_laws (Calls.fn_enc C) -> encoding_laws (Calls.site_enc C) ->
  encoding_laws (Ctx.ctx_enc cx) ->
  post_solution (Summary.lat sp) (Analysis.system (ctx_summary_analysis C cx sp)) sigma ->
  forall f k, In f (Calls.functions C) -> In k (Ctx.contexts cx) ->
    leb (Summary.lat sp) (Summary.local sp f) (sigma (f, k)) = true.
Proof.
  intros HF HP HK Hpost f k Hf Hk.
  destruct (ctx_row_spec C cx sp (Summary.SLocal f, k) sigma HF HP HK
    (proj2 (ctx_row_member C cx _ _) (conj Hk (local_row C f Hf))))
    as [Hr [Ht [Hv Hs]]].
  specialize (Hpost _ Hr); rewrite Ht, Hv in Hpost; exact (proj1 Hpost).
Qed.

(** An admitted call reads the entered context and bounds the lifted callee value. *)
Theorem ctx_call_bound {F P K A} (C : Calls.t F P) (cx : Ctx.t F P K)
    (sp : Summary.spec F P A) sigma :
  encoding_laws (Calls.fn_enc C) -> encoding_laws (Calls.site_enc C) ->
  encoding_laws (Ctx.ctx_enc cx) ->
  post_solution (Summary.lat sp) (Analysis.system (ctx_summary_analysis C cx sp)) sigma ->
  forall f p g k k', In f (Calls.functions C) -> In p (Calls.sites_of C f) ->
    In g (Calls.resolve C p) -> In k (Ctx.contexts cx) ->
    Ctx.enter cx p g k = Some k' ->
    leb (Summary.lat sp) (Summary.via_call sp p g (sigma (g, k')))
      (sigma (Calls.caller_of C p, k)) = true.
Proof.
  intros HF HP HK Hpost f p g k k' Hf Hp Hg Hk Henter.
  destruct (ctx_row_spec C cx sp (Summary.SCall p g, k) sigma HF HP HK
    (proj2 (ctx_row_member C cx _ _) (conj Hk (call_row C f p g Hf Hp Hg))))
    as [Hr [Ht [Hv Hs]]].
  specialize (Hpost _ Hr); rewrite Ht, Hv in Hpost.
  unfold Summary.ctx_get_c in Hpost; autorewrite with galois_cost in Hpost.
  fold (Ctx.enter cx p g k) in Hpost; rewrite Henter in Hpost.
  exact (proj1 Hpost).
Qed.

(** Support closure requires explicit seed membership and admitted-enter closure. *)
Record ctx_support {F P K} (C : Calls.t F P) (cx : Ctx.t F P K) : Prop := {
  ctx_initial_member : forall f, In f (Calls.roots C) ->
    In (Ctx.init cx f) (Ctx.contexts cx);
  ctx_enter_closed : forall f p g k k', In f (Calls.functions C) ->
    In k (Ctx.contexts cx) ->
    In p (Calls.sites_of C f) -> In g (Calls.resolve C p) ->
    Ctx.enter cx p g k = Some k' -> In k' (Ctx.contexts cx)
}.
Arguments ctx_initial_member {F P K C cx}.
Arguments ctx_enter_closed {F P K C cx}.

(** Reachable context equations are generated by roots and admitted resolved calls. *)
Inductive ctx_reachable {F P K} (C : Calls.t F P) (cx : Ctx.t F P K) : F -> K -> Prop :=
  | ctx_root f : In f (Calls.roots C) -> ctx_reachable C cx f (Ctx.init cx f)
  | ctx_call f k p g k' :
      ctx_reachable C cx f k ->
      In p (Calls.sites_of C f) ->
      In g (Calls.resolve C p) ->
      Ctx.enter cx p g k = Some k' ->
      ctx_reachable C cx g k'.

(** Reachable contexts lie in finite support when its explicit closure duties hold. *)
Theorem ctx_reachable_supported {F P K} (C : Calls.t F P) (cx : Ctx.t F P K) :
  graph_wf (Calls.graph C) -> ctx_support C cx ->
  forall f k, ctx_reachable C cx f k ->
    In f (Calls.functions C) /\ In k (Ctx.contexts cx).
Proof.
  intros Hwf Hsupport f k Hreach; induction Hreach as
    [f Hroot|f k p g k' Hreach [Hf Hk] Hp Hg Henter].
  - split; [exact (entries_in Hwf f Hroot)|apply (ctx_initial_member Hsupport); assumption].
  - split.
    + exact (out_target_in Hwf f (CallEdge p g) Hf (call_graph_edge C f p g Hp Hg)).
    + eapply (ctx_enter_closed Hsupport); eassumption.
Qed.

(** The inductive relation is the least family closed under the context equations.
    This replaces the relational leastness argument of reachable_callstrings_least. *)
Theorem ctx_reachable_least {F P K} (C : Calls.t F P) (cx : Ctx.t F P K)
    (R : F -> K -> Prop) :
  (forall f, In f (Calls.roots C) -> R f (Ctx.init cx f)) ->
  (forall f k p g k', R f k -> In p (Calls.sites_of C f) ->
    In g (Calls.resolve C p) -> Ctx.enter cx p g k = Some k' -> R g k') ->
  forall f k, ctx_reachable C cx f k -> R f k.
Proof.
  intros Hroot Hcall f k Hreach; induction Hreach; eauto.
Qed.

(** Reachability satisfies the context equations without an inventory-enumeration premise. *)
Theorem ctx_reachable_equation {F P K} (C : Calls.t F P) (cx : Ctx.t F P K) f k :
  ctx_reachable C cx f k <->
    (In f (Calls.roots C) /\ k = Ctx.init cx f) \/
    exists caller c p, ctx_reachable C cx caller c /\
      In p (Calls.sites_of C caller) /\ In f (Calls.resolve C p) /\
      Ctx.enter cx p f c = Some k.
Proof.
  split.
  - intro Hreach; destruct Hreach as [f Hroot|caller c p f k Hreach Hp Hf Henter].
    + left; auto.
    + right; exists caller, c, p; auto.
  - intros [[Hroot ->]|[caller [c [p [Hreach [Hp [Hf Henter]]]]]]].
    + constructor; exact Hroot.
    + eapply ctx_call; eassumption.
Qed.

(** Context frames retain each suspended caller's context so returns restore it exactly. *)
Inductive ctx_frames {F P K} (C : Calls.t F P) (cx : Ctx.t F P K) :
    F -> K -> list (F * P) -> list K -> Prop :=
  | ctx_frames_root f : In f (Calls.roots C) ->
      ctx_frames C cx f (Ctx.init cx f) [] []
  | ctx_frames_push f k rest ks p g k' :
      ctx_frames C cx f k rest ks ->
      In p (Calls.sites_of C f) ->
      In g (Calls.resolve C p) ->
      Ctx.enter cx p g k = Some k' ->
      ctx_frames C cx g k' ((f, p) :: rest) (k :: ks).

(** Matched context frames give an inductively reachable context at their top. *)
Theorem ctx_frames_reachable {F P K} (C : Calls.t F P) (cx : Ctx.t F P K)
    f k stack ks :
  ctx_frames C cx f k stack ks -> ctx_reachable C cx f k.
Proof.
  intro Hframes; induction Hframes.
  - apply ctx_root; assumption.
  - eapply ctx_call; eassumption.
Qed.

(** An inventoried matched frame chain has a supported current context. *)
Theorem ctx_frames_supported {F P K} (C : Calls.t F P) (cx : Ctx.t F P K)
    f k stack ks :
  ctx_support C cx -> ctx_frames C cx f k stack ks ->
  incl (f :: map fst stack) (Calls.functions C) -> In k (Ctx.contexts cx).
Proof.
  intros Hsupport Hframes; induction Hframes; intro Hlisted.
  - apply (ctx_initial_member Hsupport); assumption.
  - eapply (ctx_enter_closed Hsupport); try eassumption.
    + apply Hlisted; right; left; reflexivity.
    + apply IHHframes; intros h Hh; apply Hlisted; now right.
Qed.

(** A post-solution covers every activation in a context-annotated matched frame chain. *)
Theorem ctx_frames_cover {S O F P K A} (m : semantics S O) (C : Calls.t F P)
    (cl : CallsLink.t S F P) (cx : Ctx.t F P K) (sp : Summary.spec F P A)
    (sc : step_cover S O A) sigma :
  encoding_laws (Calls.fn_enc C) -> encoding_laws (Calls.site_enc C) ->
  encoding_laws (Ctx.ctx_enc cx) -> ctx_support C cx ->
  calls_laws m C cl -> summary_laws m C cl sp sc ->
  post_solution (Summary.lat sp) (Analysis.system (ctx_summary_analysis C cx sp)) sigma ->
  forall s l t, reachable_state m s -> step m s l t ->
  forall g k stack ks, ctx_frames C cx g k stack ks ->
    incl stack (CallsLink.frames cl s) -> incl (map fst stack) (Calls.functions C) ->
    step_covers sc (sigma (g, k)) s l t ->
    forall i f c, nth_error (g :: map fst stack) i = Some f ->
      nth_error (k :: ks) i = Some c -> step_covers sc (sigma (f, c)) s l t.
Proof.
  intros HF HP HK Hsupport Hcalls Hlaws Hpost s l t Hreach Hstep g k stack ks Hframes.
  induction Hframes as [g Hroot|caller c rest ks p g k Hframes IH Hp Hg Henter];
    intros Hstack Hlisted Hcover [|i] f d Hf Hd.
  - cbn in Hf, Hd; inversion Hf; inversion Hd; subst; exact Hcover.
  - destruct i; discriminate Hf.
  - cbn in Hf, Hd; inversion Hf; inversion Hd; subst; exact Hcover.
  - cbn in Hf, Hd; eapply IH; [| | |exact Hf|exact Hd].
    + intros fr Hfr; apply Hstack; now right.
    + intros h Hh; apply Hlisted; now right.
    + eapply (covers_monotone Hlaws _ _); [|exact Hreach|exact Hstep|].
      * rewrite <- (sites_caller Hcalls caller p Hp).
        eapply ctx_call_bound;
          [exact HF|exact HP|exact HK|exact Hpost| |exact Hp|exact Hg| |exact Henter].
        -- apply Hlisted; left; reflexivity.
        -- apply (ctx_frames_supported C cx _ _ _ _ Hsupport Hframes).
           exact Hlisted.
      * apply (call_covers Hlaws p g _ s l t Hreach Hstep).
        -- replace (Calls.caller_of C p) with caller.
           ++ apply Hstack; left; reflexivity.
           ++ symmetry; eapply sites_caller; eassumption.
        -- exact Hcover.
Qed.

(** Lower-level context soundness uses an established matched annotation invariant.
    Clients can derive that invariant from local duties through ctx_sound_local. *)
Theorem ctx_sound {S O F P K A} (m : semantics S O) (C : Calls.t F P)
    (cl : CallsLink.t S F P) (cx : Ctx.t F P K) (sp : Summary.spec F P A)
    (sc : step_cover S O A) sigma (context : S -> K) (suspended : S -> list K) :
  encoding_laws (Calls.fn_enc C) -> encoding_laws (Calls.site_enc C) ->
  encoding_laws (Ctx.ctx_enc cx) -> ctx_support C cx ->
  calls_laws m C cl -> summary_laws m C cl sp sc ->
  (forall s, reachable_state m s ->
    ctx_frames C cx (CallsLink.here cl s) (context s) (CallsLink.frames cl s) (suspended s)) ->
  post_solution (Summary.lat sp) (Analysis.system (ctx_summary_analysis C cx sp)) sigma ->
  forall s l t i f k, reachable_state m s -> step m s l t ->
    nth_error (Calls.active cl s) i = Some f ->
    nth_error (context s :: suspended s) i = Some k ->
    step_covers sc (sigma (f, k)) s l t.
Proof.
  intros HF HP HK Hsupport Hcalls Hlaws Hagree Hpost s l t i f k Hreach Hstep Hf Hk.
  eapply (ctx_frames_cover m C cl cx sp sc sigma HF HP HK Hsupport Hcalls Hlaws Hpost
    s l t Hreach Hstep _ _ _ _ (Hagree s Hreach)).
  - apply incl_refl.
  - intros g Hg; apply (frames_listed Hcalls s Hreach); now right.
  - eapply (covers_monotone Hlaws _ _); [|exact Hreach|exact Hstep|].
    + apply (ctx_local_bound C cx sp sigma HF HP HK Hpost).
      * apply (frames_listed Hcalls s Hreach); left; reflexivity.
      * apply (ctx_frames_supported C cx _ _ _ _ Hsupport (Hagree s Hreach)).
        exact (frames_listed Hcalls s Hreach).
    + exact (local_covers Hlaws s l t Hreach Hstep).
  - exact Hf.
  - exact Hk.
Qed.

(** Annotation duties describe initialization and each concrete step's context update.
    Entry acceptance is required only in the push alternative of an actual reachable step. *)
Record ctx_annotation_laws {S O F P K} (m : semantics S O) (C : Calls.t F P)
    (cl : CallsLink.t S F P) (cx : Ctx.t F P K)
    (context : S -> K) (suspended : S -> list K) : Prop := {
  ctx_annotation_initial : forall s, initial m s ->
    context s = Ctx.init cx (CallsLink.here cl s) /\ suspended s = [];
  ctx_annotation_step : on_steps m (fun s _ t =>
    (CallsLink.here cl t = CallsLink.here cl s /\
      CallsLink.frames cl t = CallsLink.frames cl s /\
      context t = context s /\ suspended t = suspended s) \/
    (exists p, In p (Calls.sites_of C (CallsLink.here cl s)) /\
      In (CallsLink.here cl t) (Calls.resolve C p) /\
      CallsLink.frames cl t = (CallsLink.here cl s, p) :: CallsLink.frames cl s /\
      Ctx.enter cx p (CallsLink.here cl t) (context s) = Some (context t) /\
      suspended t = context s :: suspended s) \/
    (exists f p k ks, CallsLink.frames cl s = (f, p) :: CallsLink.frames cl t /\
      CallsLink.here cl t = f /\ suspended s = k :: ks /\
      context t = k /\ suspended t = ks))
}.
Arguments ctx_annotation_initial {S O F P K m C cl cx context suspended}.
Arguments ctx_annotation_step {S O F P K m C cl cx context suspended}.

(** Initial and step-local annotation duties establish the reachable structural invariant. *)
Theorem ctx_annotations_reachable {S O F P K} (m : semantics S O) (C : Calls.t F P)
    (cl : CallsLink.t S F P) (cx : Ctx.t F P K) context suspended :
  calls_laws m C cl -> ctx_annotation_laws m C cl cx context suspended ->
  forall s, reachable_state m s ->
    ctx_frames C cx (CallsLink.here cl s) (context s) (CallsLink.frames cl s) (suspended s).
Proof.
  intros Hcalls Hannotations; apply reachable_ind.
  - intros s Hinit.
    destruct (ctx_annotation_initial Hannotations s Hinit) as [Hcontext Hsaved].
    destruct (initial_roots Hcalls s Hinit) as [Hroot Hframes].
    rewrite Hcontext, Hsaved, Hframes; constructor; exact Hroot.
  - intros s l t Hreach IH Hstep.
    destruct (ctx_annotation_step Hannotations s l t Hreach Hstep) as
      [[Hhere [Hframes [Hcontext Hsaved]]]|
        [[p [Hp [Hg [Hframes [Henter Hsaved]]]]]|
          [f [p [k [ks [Hframes [Hhere [Hsource [Hcontext Hsaved]]]]]]]]]].
    + rewrite Hhere, Hframes, Hcontext, Hsaved; exact IH.
    + rewrite Hframes, Hsaved; econstructor; eassumption.
    + rewrite Hframes, Hsource in IH; inversion IH; subst; assumption.
Qed.

(** The generic client boundary proves contextual soundness from initial and local step duties.
    It accepts partial entry policies and contains no global annotation or result assumption. *)
Theorem ctx_sound_local {S O F P K A} (m : semantics S O) (C : Calls.t F P)
    (cl : CallsLink.t S F P) (cx : Ctx.t F P K) (sp : Summary.spec F P A)
    (sc : step_cover S O A) sigma context suspended :
  encoding_laws (Calls.fn_enc C) -> encoding_laws (Calls.site_enc C) ->
  encoding_laws (Ctx.ctx_enc cx) -> ctx_support C cx ->
  calls_laws m C cl -> summary_laws m C cl sp sc ->
  ctx_annotation_laws m C cl cx context suspended ->
  post_solution (Summary.lat sp) (Analysis.system (ctx_summary_analysis C cx sp)) sigma ->
  forall s l t i f k, reachable_state m s -> step m s l t ->
    nth_error (Calls.active cl s) i = Some f ->
    nth_error (context s :: suspended s) i = Some k ->
    step_covers sc (sigma (f, k)) s l t.
Proof.
  intros HF HP HK Hsupport Hcalls Hsummary Hannotations Hpost.
  apply (ctx_sound m C cl cx sp sc sigma context suspended
    HF HP HK Hsupport Hcalls Hsummary).
  - exact (ctx_annotations_reachable m C cl cx context suspended Hcalls Hannotations).
  - exact Hpost.
Qed.

(** Call-string entry keeps exactly the bounded innermost sites. *)
Theorem ctx_call_string_enter {F P} (C : Calls.t F P) bound p g st :
  Ctx.enter (Ctx.call_string bound C) p g st =
    Some (Stack.truncate bound (p :: st)).
Proof.
  unfold Ctx.enter, Ctx.call_string; cbn [Ctx.enter_c].
  rewrite Cost.value_map, Ctx.take_value; reflexivity.
Qed.

Local Lemma strings_empty {P} bound (sites : list P) :
  In [] (Cost.value (Ctx.strings_c bound sites)).
Proof.
  destruct bound; cbn [Ctx.strings_c]; autorewrite with galois_cost; now left.
Qed.

Local Lemma strings_step {P} bound (sites : list P) p st :
  In p sites -> In st (Cost.value (Ctx.strings_c bound sites)) ->
  In (Stack.truncate bound (p :: st)) (Cost.value (Ctx.strings_c bound sites)).
Proof.
  revert p st; induction bound as [|bound IH]; intros p st Hp Hst.
  - change (In (@nil P) [@nil P]); now left.
  - cbn [Ctx.strings_c] in Hst |- *; autorewrite with galois_cost in Hst |- *.
    rewrite fw_flat_map_value in Hst |- *.
    right; apply in_flat_map; exists p; split; [exact Hp|].
    rewrite value_map_c.
    change (In (p :: firstn bound st)
      (map (fun xs => p :: xs) (Cost.value (Ctx.strings_c bound sites)))).
    apply in_map.
    destruct Hst as [<-|Hst].
    + rewrite firstn_nil; apply strings_empty.
    + apply in_flat_map in Hst; destruct Hst as [q [Hq Hst]].
      rewrite value_map_c in Hst; apply in_map_iff in Hst.
      destruct Hst as [xs [Heq Hxs]]; cbn in Heq; subst st.
      apply IH; assumption.
Qed.

(** The reference call-string inventory satisfies explicit seed and entry closure laws. *)
Theorem ctx_call_string_support {F P} (C : Calls.t F P) bound :
  ctx_support C (Ctx.call_string bound C).
Proof.
  set (sites := flat_map (Calls.sites_of C) (Calls.functions C)).
  assert (Hsites : Cost.value (fw_flat_map_c (Calls.sites_of_c C) (Calls.functions C)) =
    sites) by (rewrite fw_flat_map_value; reflexivity).
  constructor.
  - intros f Hroot; unfold Ctx.call_string; rewrite Hsites; apply strings_empty.
  - intros f p g k k' Hf Hk Hp Hg Henter.
    rewrite ctx_call_string_enter in Henter; inversion Henter; subst k'.
    unfold Ctx.call_string in Hk |- *; rewrite Hsites in Hk |- *.
    apply strings_step; [|exact Hk].
    unfold sites; apply in_flat_map; exists f; auto.
Qed.

(** A bounded context push agrees with pushing on the full matched stack. *)
Theorem ctx_truncate_push {P} bound p (st : list P) :
  Stack.truncate bound (p :: Stack.truncate bound st) =
    Stack.truncate bound (p :: st).
Proof.
  destruct bound as [|bound]; [reflexivity|].
  change (p :: firstn bound (firstn (S bound) st) = p :: firstn bound st).
  rewrite firstn_firstn, Nat.min_l by lia; reflexivity.
Qed.

(** Call strings at matched activations are exactly the truncated suspended call-site stack. *)
Theorem ctx_reachable_call_string {F P} (C : Calls.t F P) bound f k stack ks :
  ctx_frames C (Ctx.call_string bound C) f k stack ks ->
  k = Stack.truncate bound (map snd stack).
Proof.
  intro Hframes; induction Hframes as [f Hroot|f k rest ks p g k' Hframes IH Hp Hg He].
  - change ((@nil P) = firstn bound (@nil P)); rewrite firstn_nil; reflexivity.
  - rewrite ctx_call_string_enter in He; inversion He; subst k'.
    rewrite IH, ctx_truncate_push; reflexivity.
Qed.

(** Accepted pushes and matched returns preserve existence of a context annotation. *)
Theorem ctx_frames_step {S O F P K} (m : semantics S O) (C : Calls.t F P)
    (cl : CallsLink.t S F P) (cx : Ctx.t F P K) :
  calls_laws m C cl ->
  (forall p g k, exists k', Ctx.enter cx p g k = Some k') ->
  on_steps m (fun s _ t =>
    (exists k ks, ctx_frames C cx (CallsLink.here cl s) k (CallsLink.frames cl s) ks) ->
    exists k ks, ctx_frames C cx (CallsLink.here cl t) k (CallsLink.frames cl t) ks).
Proof.
  intros Hcalls Htotal s l t Hreach Hstep [k [ks Hframes]].
  destruct (step_shape Hcalls s l t Hreach Hstep) as
    [[Hhere Hstack]|[[p [Hp [Hg Hstack]]]|[f [p [Hstack Hhere]]]]].
  - rewrite Hhere, Hstack; now exists k, ks.
  - destruct (Htotal p (CallsLink.here cl t) k) as [k' Henter].
    rewrite Hstack; exists k', (k :: ks); econstructor; eassumption.
  - rewrite Hstack in Hframes; inversion Hframes; subst.
    eauto.
Qed.

(** Every reachable state has a matched annotation when the context policy admits calls. *)
Theorem ctx_reachable_state {S O F P K} (m : semantics S O) (C : Calls.t F P)
    (cl : CallsLink.t S F P) (cx : Ctx.t F P K) :
  calls_laws m C cl ->
  (forall p g k, exists k', Ctx.enter cx p g k = Some k') ->
  forall s, reachable_state m s ->
    exists k ks, ctx_frames C cx (CallsLink.here cl s) k (CallsLink.frames cl s) ks.
Proof.
  intros Hcalls Htotal; apply reachable_ind.
  - intros s Hinit; destruct (initial_roots Hcalls s Hinit) as [Hroot Hstack].
    rewrite Hstack; exists (Ctx.init cx (CallsLink.here cl s)), [].
    constructor; exact Hroot.
  - intros s l t Hreach IH Hstep.
    exact (ctx_frames_step m C cl cx Hcalls Htotal s l t Hreach Hstep IH).
Qed.

(** A matched stack step has the stack change declared by its edge kind. *)
Theorem ctx_stack_step_shape {N E P D} (I : Ifds.t N E P D) c e d :
  Stack.step I c e d ->
  match Icfg.edge_kind (Ifds.icfg I) e with
  | Icfg.Internal => snd d = snd c
  | Icfg.Call p => snd d = p :: snd c
  | Icfg.Return p => snd c = p :: snd d
  end.
Proof.
  intro Hstep; destruct Hstep as
    [e x y st He Hkind Hflow|e p x y st He Hkind Hflow|e p x y st He Hkind Hflow];
    rewrite Hkind; reflexivity.
Qed.

(** Silent stack semantics uses the inductive matched-stack step as its transition relation. *)
Definition ctx_stack_semantics {N E P D} (I : Ifds.t N E P D)
    (roots : list (Stack.config N D P)) : semantics (Stack.config N D P) unit :=
  Semantics (fun c => In c roots)
    (fun c l d => l = [] /\ exists e, Stack.step I c e d).

Local Lemma ctx_stack_path_exec {N E P D} (I : Ifds.t N E P D) roots c d :
  Stack.path I c d -> exec (ctx_stack_semantics I roots) c [] d.
Proof.
  intro Hpath; induction Hpath as [c|c e d z Hstep Hpath IH].
  - constructor.
  - change (exec (ctx_stack_semantics I roots) c ([] ++ []) z).
    eapply exec_step with (s' := d).
    + split; [reflexivity|exists e; exact Hstep].
    + exact IH.
Qed.

(** Semantic context reachability follows actual matched paths, including their return checks. *)
Theorem ctx_matched_path {N E P D F K} (I : Ifds.t N E P D) roots
    (C : Calls.t F P) (cl : CallsLink.t (Stack.config N D P) F P)
    (cx : Ctx.t F P K) c n d st :
  calls_laws (ctx_stack_semantics I roots) C cl ->
  (forall p g k, exists k', Ctx.enter cx p g k = Some k') ->
  (forall n d st, map snd (CallsLink.frames cl (n, d, st)) = st) ->
  In c roots -> Stack.path I c (n, d, st) ->
  exists k frames ks, ctx_frames C cx (CallsLink.here cl (n, d, st)) k frames ks /\
    map snd frames = st /\ ctx_reachable C cx (CallsLink.here cl (n, d, st)) k.
Proof.
  intros Hcalls Htotal Hstack Hroot Hpath.
  assert (Hreach : reachable_state (ctx_stack_semantics I roots) (n, d, st)).
  { exists c, []; split; [exact Hroot|now apply ctx_stack_path_exec]. }
  destruct (ctx_reachable_state _ C cl cx Hcalls Htotal _ Hreach) as [k [ks Hframes]].
  exists k, (CallsLink.frames cl (n, d, st)), ks.
  split; [exact Hframes|split; [apply Hstack|eapply ctx_frames_reachable; exact Hframes]].
Qed.

(** Call-string contexts reached by matched paths equal the truncated concrete stack. *)
Theorem ctx_matched_call_string {N E P D F} (I : Ifds.t N E P D) roots
    (C : Calls.t F P) (cl : CallsLink.t (Stack.config N D P) F P) bound c n d st :
  calls_laws (ctx_stack_semantics I roots) C cl ->
  (forall n d st, map snd (CallsLink.frames cl (n, d, st)) = st) ->
  In c roots -> Stack.path I c (n, d, st) ->
  ctx_reachable C (Ctx.call_string bound C) (CallsLink.here cl (n, d, st))
    (Stack.truncate bound st).
Proof.
  intros Hcalls Hstack Hroot Hpath.
  destruct (ctx_matched_path I roots C cl (Ctx.call_string bound C) c n d st
    Hcalls ltac:(intros p g k; eexists; apply ctx_call_string_enter)
    Hstack Hroot Hpath) as [k [frames [ks [Hframes [Hsites Hreach]]]]].
  pose proof (ctx_reachable_call_string C bound _ _ _ _ Hframes) as Heq.
  rewrite Hsites in Heq; now subst k.
Qed.

(** Supported contextual post-solutions satisfy exactly local and admitted-call inequalities. *)
Theorem ctx_post_solution_iff {F P K A} (C : Calls.t F P) (cx : Ctx.t F P K)
    (sp : Summary.spec F P A) sigma :
  encoding_laws (Calls.fn_enc C) -> encoding_laws (Calls.site_enc C) ->
  encoding_laws (Ctx.ctx_enc cx) -> lattice_laws (Summary.lat sp) ->
  (post_solution (Summary.lat sp) (Analysis.system (ctx_summary_analysis C cx sp)) sigma <->
    (forall f k, In f (Calls.functions C) -> In k (Ctx.contexts cx) ->
      leb (Summary.lat sp) (Summary.local sp f) (sigma (f, k)) = true) /\
    (forall f p g k k', In f (Calls.functions C) -> In p (Calls.sites_of C f) ->
      In g (Calls.resolve C p) -> In k (Ctx.contexts cx) ->
      Ctx.enter cx p g k = Some k' ->
      leb (Summary.lat sp) (Summary.via_call sp p g (sigma (g, k')))
        (sigma (Calls.caller_of C p, k)) = true)).
Proof.
  intros HF HP HK HL; split.
  - intro Hpost; split.
    + exact (ctx_local_bound C cx sp sigma HF HP HK Hpost).
    + exact (ctx_call_bound C cx sp sigma HF HP HK Hpost).
  - intros [Hlocal Hcall] [r k] Hr.
    assert (Hrows : System.constraints (Analysis.system (ctx_summary_analysis C cx sp)) =
      ctx_rows C cx).
    { unfold ctx_summary_analysis, Summary.ctx_analysis.
      change (Cost.value (fw_flat_map_c (fun k =>
        map_c (fun r => Cost.ret (r, k)) (Cost.value (Summary.rows_c C)))
        (Ctx.contexts cx)) = ctx_rows C cx).
      rewrite fw_flat_map_value; unfold ctx_rows; apply flat_map_ext; intro c.
      rewrite value_map_c; reflexivity. }
    rewrite Hrows in Hr.
    destruct (ctx_row_spec C cx sp (r, k) sigma HF HP HK Hr) as [_ [Ht [Hv Hs]]].
    rewrite Ht, Hv, Hs; split; [|intros x a Hbad; contradiction].
    apply ctx_row_member in Hr; destruct Hr as [Hk Hr].
    rewrite rows_equation in Hr; destruct r as [f|p g].
    + apply Hlocal; [|exact Hk].
      apply in_app_or in Hr; destruct Hr as [Hr|Hr].
      * apply in_map_iff in Hr; destruct Hr as [h [Heq Hh]]; inversion Heq; subst h; exact Hh.
      * apply in_flat_map in Hr; destruct Hr as [h [_ Hr]].
        apply in_flat_map in Hr; destruct Hr as [q [_ Hr]].
        apply in_map_iff in Hr; destruct Hr as [g [Heq _]]; discriminate.
    + unfold Summary.ctx_get_c; autorewrite with galois_cost.
      fold (Ctx.enter cx p g k); destruct (Ctx.enter cx p g k) as [k'|] eqn:Henter.
      * apply in_app_or in Hr; destruct Hr as [Hr|Hr].
        -- apply in_map_iff in Hr; destruct Hr as [h [Heq _]]; discriminate.
        -- apply in_flat_map in Hr; destruct Hr as [f [Hf Hr]].
           apply in_flat_map in Hr; destruct Hr as [q [Hq Hr]].
           apply in_map_iff in Hr; destruct Hr as [h [Heq Hh]]; inversion Heq; subst q h.
           exact (Hcall f p g k k' Hf Hq Hh Hk Henter).
      * apply (bot_least HL).
Qed.

(** Insensitive contexts and ordinary summaries have exactly the same post-solution equations. *)
Theorem ctx_insensitive_agrees {F P A} (C : Calls.t F P) (sp : Summary.spec F P A)
    (sigma : F * unit -> A) :
  encoding_laws (Calls.fn_enc C) -> encoding_laws (Calls.site_enc C) ->
  lattice_laws (Summary.lat sp) ->
  (post_solution (Summary.lat sp)
      (Analysis.system (ctx_summary_analysis C (Ctx.insensitive F P) sp)) sigma <->
    post_solution (Summary.lat sp) (Analysis.system (summary_analysis C sp))
      (fun f => sigma (f, tt))).
Proof.
  intros HF HP HL.
  rewrite (ctx_post_solution_iff C (Ctx.insensitive F P) sp sigma HF HP
    unit_encoding_laws HL), (post_solution_iff C sp _ HF HP).
  split; intros [Hlocal Hcall]; split.
  - intros f Hf; apply Hlocal; [exact Hf|left; reflexivity].
  - intros f p g Hf Hp Hg; exact (Hcall f p g tt tt Hf Hp Hg (or_introl eq_refl) eq_refl).
  - intros f [] Hf Hk; apply Hlocal; exact Hf.
  - intros f p g [] [] Hf Hp Hg Hk Henter; exact (Hcall f p g Hf Hp Hg).
Qed.

(** Insensitive and ordinary least results agree pointwise in the lattice preorder. *)
Theorem ctx_insensitive_least_agrees {F P A} (C : Calls.t F P)
    (sp : Summary.spec F P A) (sigma : F * unit -> A) tau :
  encoding_laws (Calls.fn_enc C) -> encoding_laws (Calls.site_enc C) ->
  lattice_laws (Summary.lat sp) ->
  least_solution (Summary.lat sp)
    (Analysis.system (ctx_summary_analysis C (Ctx.insensitive F P) sp)) sigma ->
  least_solution (Summary.lat sp) (Analysis.system (summary_analysis C sp)) tau ->
  forall f, equivalent (Summary.lat sp) (sigma (f, tt)) (tau f).
Proof.
  intros HF HP HL [Hctx Hctxleast] [Hsum Hsumleast] f; split.
  - apply (Hctxleast (fun fk => tau (fst fk))).
    apply (proj2 (ctx_insensitive_agrees C sp _ HF HP HL)); exact Hsum.
  - exact (Hsumleast (fun f => sigma (f, tt))
      (proj1 (ctx_insensitive_agrees C sp sigma HF HP HL) Hctx) f).
Qed.

(** An annotation has one saved context per suspended frame. *)
Theorem ctx_frames_length {F P K} (C : Calls.t F P) (cx : Ctx.t F P K)
    f k stack ks :
  ctx_frames C cx f k stack ks -> length ks = length stack.
Proof.
  intro Hframes; induction Hframes; cbn; congruence.
Qed.

Local Lemma ctx_call_string_at {F P} (C : Calls.t F P) bound f k stack ks :
  ctx_frames C (Ctx.call_string bound C) f k stack ks ->
  forall i c, nth_error (k :: ks) i = Some c ->
    c = Stack.truncate bound (map snd (skipn i stack)).
Proof.
  intro Hframes; induction Hframes as [f Hroot|f k rest ks p g k' Hframes IH Hp Hg He];
    intros [|i] c Hc.
  - cbn in Hc; inversion Hc; subst c.
    change ((@nil P) = firstn bound (@nil P)); now rewrite firstn_nil.
  - destruct i; discriminate Hc.
  - cbn in Hc; inversion Hc; subst c.
    exact (ctx_reachable_call_string C bound _ _ _ _
      (ctx_frames_push C (Ctx.call_string bound C) f k rest ks p g k' Hframes Hp Hg He)).
  - cbn in Hc; cbn [skipn]; apply IH; exact Hc.
Qed.

(** Every active function's bounded call-string summary covers every reachable concrete step. *)
Theorem ctx_call_string_sound {S O F P A} (m : semantics S O) (C : Calls.t F P)
    (cl : CallsLink.t S F P) bound (sp : Summary.spec F P A) (sc : step_cover S O A) sigma :
  encoding_laws (Calls.fn_enc C) -> encoding_laws (Calls.site_enc C) ->
  calls_laws m C cl -> summary_laws m C cl sp sc ->
  post_solution (Summary.lat sp)
    (Analysis.system (ctx_summary_analysis C (Ctx.call_string bound C) sp)) sigma ->
  forall s l t i f, reachable_state m s -> step m s l t ->
    nth_error (Calls.active cl s) i = Some f ->
    step_covers sc (sigma (f, Stack.truncate bound
      (map snd (skipn i (CallsLink.frames cl s))))) s l t.
Proof.
  intros HF HP Hcalls Hlaws Hpost s l t i f Hreach Hstep Hf.
  set (cx := Ctx.call_string bound C).
  assert (HK : encoding_laws (Ctx.ctx_enc cx)).
  { apply FrameworkKey.list_laws; exact HP. }
  destruct (ctx_reachable_state m C cl cx Hcalls
    ltac:(intros p g k; eexists; apply ctx_call_string_enter) s Hreach)
    as [k [ks Hframes]].
  assert (Hlength : length (k :: ks) = length (Calls.active cl s)).
  { cbn; unfold Calls.active; cbn; rewrite length_map.
    rewrite (ctx_frames_length C cx _ _ _ _ Hframes); reflexivity. }
  destruct (nth_error (k :: ks) i) as [c|] eqn:Hc.
  - rewrite <- (ctx_call_string_at C bound _ _ _ _ Hframes i c Hc).
    eapply (ctx_frames_cover m C cl cx sp sc sigma HF HP HK
      (ctx_call_string_support C bound) Hcalls Hlaws Hpost s l t Hreach Hstep
      _ _ _ _ Hframes).
    + apply incl_refl.
    + intros g Hg; apply (frames_listed Hcalls s Hreach); now right.
    + eapply (covers_monotone Hlaws _ _); [|exact Hreach|exact Hstep|].
      * apply (ctx_local_bound C cx sp sigma HF HP HK Hpost).
        -- apply (frames_listed Hcalls s Hreach); left; reflexivity.
        -- apply (ctx_frames_supported C cx _ _ _ _ (ctx_call_string_support C bound) Hframes).
           exact (frames_listed Hcalls s Hreach).
      * exact (local_covers Hlaws s l t Hreach Hstep).
    + exact Hf.
    + exact Hc.
  - apply nth_error_None in Hc; rewrite Hlength in Hc.
    assert (Hsome : nth_error (Calls.active cl s) i <> None) by (rewrite Hf; discriminate).
    apply nth_error_Some in Hsome; lia.
Qed.

End SummarySound.
