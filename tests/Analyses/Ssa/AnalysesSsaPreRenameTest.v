(** * Scoped-frame origins, point paths and checked histories

    These clients keep entry values separate from unavailable sentinels and test ordered folds.
    For example, a failed local precondition excludes a checked history with the same endpoint.
    Builds on: AnalysesSsaPreRename, AnalysesSsaPreFrameStep and AnalysesSsaPreContextTest. *)

From Stdlib Require Import List Bool Arith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseMap.
From Galois.Graph Require Import GraphModel GraphDomSpec.
From Galois.Analyses.Ssa Require Import AnalysesSsaPreContext AnalysesSsaPreFrg
  AnalysesSsaPreRename AnalysesSsaPreCoverage AnalysesSsaPreFrameStep.
From Galois.Tests.Analyses.Ssa Require Import AnalysesSsaPreContextTest.
Import List.ListNotations.

Example initial_scope_value :
  PreRename.top One.ctx (PreRename.initial_scope One.ctx [tt]) tt =
    PreRename.Frame (PreFrg.Operand (PreFrg.Initial tt) false) true.
Proof.
  vm_compute; reflexivity.
Qed.

Example missing_scope_value :
  PreRename.top One.ctx Map.empty tt =
    PreRename.Frame (PreFrg.Operand (PreFrg.Unavailable tt) false) false.
Proof.
  vm_compute; reflexivity.
Qed.

Example internal_projection :
  PreRename.project_edges One.ctx [tt; tt] = [].
Proof.
  vm_compute; reflexivity.
Qed.

Example parallel_projection_order :
  PreRename.project_edges Parallel.ctx [true; false; true] = [true; false; true].
Proof.
  vm_compute; reflexivity.
Qed.

(** The projection theorem preserves the endpoints of the lawful single-block instruction path. *)
Example instruction_path_client :
  path One.bg tt (PreRename.project_edges One.ctx [tt]) tt.
Proof.
  apply (PreRename.project_path One.ctx One.laws false [tt] true).
  - now left.
  - exact (@path_cons bool unit One.pg tt [] true (or_introl eq_refl) (path_nil true)).
Qed.

Definition entry_graph : PreFrg.frg unit unit unit unit :=
  PreFrg.Frg [PreFrg.Unavailable tt; PreFrg.Initial tt]
    Map.empty Map.empty Map.empty Map.empty Map.empty.

(** The initial value is nearest at the actual entry in an inhabited context. *)
Example initial_nearest :
  PreRename.nearest_version One.ctx entry_graph tt false (PreFrg.Initial tt).
Proof.
  split; [now right; left|]; split; [reflexivity|].
  exists false; split; [reflexivity|]; split; [apply dominates_refl|].
  intros other p Hother _ Hpoint _.
  destruct Hother as [<-|[<-|[]]].
  - rewrite PreFrg.version_point_equation in Hpoint; discriminate.
  - rewrite PreFrg.version_point_equation in Hpoint; inversion Hpoint; subst p.
    apply dominates_refl.
Qed.

(** The entry-frame meaning carries a real nearest definition with no fictitious occurrence. *)
Example initial_frame_meaning :
  PreCoverage.frame_laws One.ctx entry_graph tt false
    (PreRename.Frame (PreFrg.Operand (PreFrg.Initial tt) false) true).
Proof.
  split; [reflexivity|]; split.
  - split; [discriminate|].
    intros [e [Hget _]]; vm_compute in Hget; discriminate.
  - split; [exact initial_nearest|].
    split; [|intros _; reflexivity].
    intros _ e Hlisted; vm_compute in Hlisted |- *; tauto.
Qed.

Definition add (n delta : nat) := n + delta.
Definition small (n delta : nat) := n + delta <= 3.

Example checked_fold_boundary :
  PreFrameStep.fold_enabled add small [1; 2] 0.
Proof.
  vm_compute; repeat split; auto.
Qed.

(** The checked-history theorem applies to the actual ordered fold and its enabled states. *)
Example checked_history_client :
  PreFrameStep.history (PreFrameStep.checked_step add small) 0 [1; 2] 3.
Proof.
  apply (proj2 (PreFrameStep.checked_history_fold add small)).
  split; [exact checked_fold_boundary|reflexivity].
Qed.

Example rejected_checked_fold :
  ~ PreFrameStep.fold_enabled add small [2; 2] 0.
Proof.
  vm_compute; lia.
Qed.
