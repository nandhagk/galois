(** * Untraced memory-phi pruning computation

    This body prepares dependencies, resolves acyclic equal inputs and returns plain graph fields.
    For example, all output representative reads occur in returned closures when they are called.
    Builds on: the unchanged phi dependency preparation and original collection operations. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet.
From Galois.Graph Require Import GraphCore GraphScc.
From Galois.Views Require Import ViewsMemoryEffects.
From Galois.Analyses Require Import AnalysesMemoryGraph AnalysesMemoryFlow
  AnalysesAuditMemoryPhiState.
Import List.ListNotations.

Definition audit_phi_compute_rep {N E} (EN : encoding N) (EE : encoding E)
    (reps : Map.t (memory_version N E) (memory_version N E)) (v : memory_version N E) :=
  match Map.get (memory_version_encoding EN EE) v reps with
  | None => v
  | Some representative => representative
  end.

Definition audit_phi_compute_step {N E} (EN : encoding N) (EE : encoding E)
    (index : phi_dependency_index (E := E) EN)
    (reps : Map.t (memory_version N E) (memory_version N E)) (node : N) :=
  if FinSet.mem EN node (phi_index_cycles index) then reps else
  match Map.get EN node (phi_index_inputs index) with
  | None | Some [] => reps
  | Some ((_, v) :: rest) =>
      let rep := audit_phi_compute_rep EN EE reps in
      let candidate := rep v in
      let code := encode (memory_version_encoding EN EE) in
      let self := Pos.eqb (code candidate) (code (MemoryPhi node)) in
      let all_same := forallb (fun kv => Pos.eqb (code candidate) (code (rep (snd kv)))) rest in
      if andb (negb self) all_same then
        Map.set (memory_version_encoding EN EE) (MemoryPhi node) candidate reps
      else reps
  end.

Definition audit_phi_compute_output {N E} (EN : encoding N) (EE : encoding E)
    (old : memory_graph N E) (reps : Map.t (memory_version N E) (memory_version N E)) :=
  let rep := audit_phi_compute_rep EN EE reps in
  let kept := filter (fun n =>
    Pos.eqb (encode (memory_version_encoding EN EE) (MemoryPhi n))
      (encode (memory_version_encoding EN EE) (rep (MemoryPhi n)))) (memory_phis old) in
  let kept_set := FinSet.of_list EN kept in
  MemoryGraph
    (filter (fun n => FinSet.mem EN n kept_set) (memory_phis old))
    (filter (fun v =>
      match v with
      | MemoryPhi n => FinSet.mem EN n kept_set
      | _ => true
      end) (memory_versions old))
    (fun n => rep (memory_in old n))
    (fun e i => option_map rep (memory_before old e i))
    (fun e => rep (memory_out old e))
    (fun n key => if FinSet.mem EN n kept_set
      then option_map rep (memory_operand old n key) else None).

Definition audit_phi_compute N E T (EN : encoding N) (EE : encoding E)
    (g : Graph.t N E) (effects : E -> list (memory_effect T)) (mg : memory_graph N E) :
    phi_result N E :=
  let index := phi_prepare_dependencies EN EE g effects mg in
  let order := concat (components (phi_index_scc index)) in
  let reps := fold_left (audit_phi_compute_step EN EE index) order Map.empty in
  @PhiResult N E (audit_phi_compute_output EN EE mg reps) reps.

Example audit_phi_plain_kept_live_fixture :
  let old : memory_graph positive positive :=
    MemoryGraph [] [MemoryLive] (fun _ => MemoryLive) (fun _ _ => None)
      (fun _ => MemoryLive) (fun _ _ => None) in
  memory_versions (audit_phi_compute_output positive_encoding positive_encoding old Map.empty) =
    [MemoryLive].
Proof.
  reflexivity.
Qed.
