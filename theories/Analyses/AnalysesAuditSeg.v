(** * Original SEG reconstruction component contract

    The helper retains the original directional reconstruction theorem type.
    For example, an absent interior returns false without invoking the cut callback.
    Builds on: SEG definitions and graph and collection audit vocabularies. *)
From Stdlib Require Import List Bool PArith ZArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditCost.
From Galois.Graph Require Import GraphCore GraphAuditBase GraphAuditDfs GraphAuditVirtual
  GraphAuditFrontier.
From Galois.Analyses Require Import AnalysesAuditSsaQueryBase AnalysesLiveness AnalysesAvailable
  AnalysesSeg.
Import List.ListNotations.

(** * Original SEG reconstruction component contract *)

Inductive audit_seg_strict_event (E U : Type) : Type :=
  | AuditSegGen (edge : E) (generated : list U)
  | AuditSegKill (edge : E) (expression : U) (killed : bool)
  | AuditSegEncode (expression : U) (code : positive)
  | AuditSegEqual (left right : positive) (answer : bool).

Arguments AuditSegGen {E U} _ _.

Arguments AuditSegKill {E U} _ _ _.

Arguments AuditSegEncode {E U} _ _.

Arguments AuditSegEqual {E U} _ _ _.

Fixpoint audit_seg_strict_mentions {E U} (EU : encoding U) (u : U) (xs : list U)
    : bool * list (audit_seg_strict_event E U) :=
  match xs with
  | [] => (false, [])
  | x :: rest =>
    let left := encode EU u in
    let right := encode EU x in
    let equal := Pos.eqb left right in
    let '(later_result, later) := audit_seg_strict_mentions EU u rest in
    (equal || later_result,
     AuditSegEncode u left :: AuditSegEncode x right :: AuditSegEqual left right equal :: later)
  end.

Definition audit_seg_strict_transfer {S O N E U C} (EU : encoding U)
    (gk : genkill_view S O N E U C) (u : U) (e : E) (b : bool)
    : bool * list (audit_seg_strict_event E U) :=
  let generated := gen gk e in
  let '(found, events) := audit_seg_strict_mentions EU u generated in
  let killed := kill gk e u in
  (found || (b && negb killed), AuditSegGen e generated :: events ++ [AuditSegKill e u killed]).

(** This relation records every comparison in the strict mention scan in occurrence order. *)
Inductive audit_seg_mentions_execution {E U} (EU : encoding U) (u : U)
    : list U -> bool -> list (audit_seg_strict_event E U) -> Prop :=
  | AuditSegMentionsNil : audit_seg_mentions_execution EU u [] false []
  | AuditSegMentionsCons x rest later_result later :
      audit_seg_mentions_execution EU u rest later_result later ->
      audit_seg_mentions_execution EU u (x :: rest)
        (Pos.eqb (encode EU u) (encode EU x) || later_result)
        (AuditSegEncode u (encode EU u) :: AuditSegEncode x (encode EU x) ::
         AuditSegEqual (encode EU u) (encode EU x)
           (Pos.eqb (encode EU u) (encode EU x)) :: later).

(** A transfer execution couples the mention scan with its generation and kill events. *)
Inductive audit_seg_transfer_execution {S O N E U C} (EU : encoding U)
    (gk : genkill_view S O N E U C) (u : U) (e : E) (b : bool)
    : bool -> list (audit_seg_strict_event E U) -> Prop :=
  | AuditSegTransferRun found events :
      audit_seg_mentions_execution EU u (gen gk e) found events ->
      audit_seg_transfer_execution EU gk u e b
        (found || (b && negb (kill gk e u)))
        (AuditSegGen e (gen gk e) :: events ++ [AuditSegKill e u (kill gk e u)]).

(** Each transfer has a recorded execution with the original bit-transfer result. *)
Definition audit_seg_transfer_execution_exists_statement : Prop :=
  forall S O N E U C (EU : encoding U) (gk : genkill_view S O N E U C) u e b,
    exists result events, audit_seg_transfer_execution EU gk u e b result events /\
      result = seg_bit_transfer EU gk u e b.

(** Strict transfer records the original result and three events per generated occurrence. *)
Definition audit_seg_strict_transfer_statement : Prop :=
  forall S O N E U C (EU : encoding U) (gk : genkill_view S O N E U C) u e b,
    let '(result, events) := audit_seg_strict_transfer EU gk u e b in
    audit_seg_transfer_execution EU gk u e b result events /\
    result = seg_bit_transfer EU gk u e b /\
    length events = 2 + 3 * length (gen gk e).

Definition audit_seg_model_event {E U} (event : audit_seg_strict_event E U) : nat :=
  match event with
  | AuditSegGen _ _ | AuditSegKill _ _ _ => 1
  | AuditSegEncode _ code => audit_encoding_weight (audit_key_bits_weight code)
  | AuditSegEqual left_code right_code _ => audit_binary_weight (Z.pos left_code) (Z.pos right_code)
  end.

Definition audit_seg_model_work {E U} (events : list (audit_seg_strict_event E U)) : nat :=
  fold_right (fun event n => audit_seg_model_event event + n) 0 events.

Definition audit_seg_model_expected {S O N E U C} (EU : encoding U)
    (gk : genkill_view S O N E U C) (u : U) (e : E) : nat :=
  2 + fold_right (fun x total =>
    audit_encoding_weight (audit_key_bits_weight (encode EU u)) +
    audit_encoding_weight (audit_key_bits_weight (encode EU x)) +
    audit_binary_weight (Z.pos (encode EU u)) (Z.pos (encode EU x)) + total)
    0 (gen gk e).

(** A transfer execution's work sums generation, kill and encoded comparison costs. *)
Definition audit_seg_model_statement : Prop :=
  forall S O N E U C (EU : encoding U) (gk : genkill_view S O N E U C) u e b result events,
    audit_seg_transfer_execution EU gk u e b result events ->
    audit_seg_model_work events = audit_seg_model_expected EU gk u e.

Inductive audit_seg_reconstruct_call (N E U : Type) : Type :=
  | AuditSegReconCase (site : nat)
  | AuditSegReconAdd (n : N) (s : FinSet.t N)
  | AuditSegReconMem (n : N) (s : FinSet.t N) (result : bool)
  | AuditSegReconInterior (n : N) (m : Map.t N (E * nat)) (result : option (E * nat))
  | AuditSegReconPath (e : E) (m : Map.t E (list E)) (result : option (list E))
  | AuditSegReconSource (e : E) (n : N)
  | AuditSegReconTarget (e : E) (n : N)
  | AuditSegReconCut (n : N) (result : bool)
  | AuditSegReconTransfer (event : audit_seg_strict_event E U).

Arguments AuditSegReconCase {N E U} _.

Arguments AuditSegReconAdd {N E U} _ _.

Arguments AuditSegReconMem {N E U} _ _ _.

Arguments AuditSegReconInterior {N E U} _ _ _.

Arguments AuditSegReconPath {N E U} _ _ _.

Arguments AuditSegReconSource {N E U} _ _.

Arguments AuditSegReconTarget {N E U} _ _.

Arguments AuditSegReconCut {N E U} _ _.

Arguments AuditSegReconTransfer {N E U} _.

Fixpoint audit_seg_recon_setup {N E U} (EN : encoding N) (nodes : list N) (cuts : FinSet.t N)
    : FinSet.t N * list (audit_seg_reconstruct_call N E U) :=
  match nodes with
  | [] => (cuts, [AuditSegReconCase 0])
  | n :: rest => let next := FinSet.add EN n cuts in
    let '(result, events) := audit_seg_recon_setup EN rest next in
    (result, AuditSegReconCase 1 :: AuditSegReconAdd n cuts :: events)
  end.

Fixpoint audit_seg_firstn {N E U} (k : nat) (xs : list E)
    : list E * list (audit_seg_reconstruct_call N E U) :=
  match k, xs with
  | O, _ => ([], [AuditSegReconCase 2])
  | S _, [] => ([], [AuditSegReconCase 3])
  | S n, e :: rest => let '(later, events) := audit_seg_firstn n rest in
    (e :: later, AuditSegReconCase 4 :: events)
  end.

Fixpoint audit_seg_skipn {N E U} (k : nat) (xs : list E)
    : list E * list (audit_seg_reconstruct_call N E U) :=
  match k, xs with
  | O, _ => (xs, [AuditSegReconCase 5])
  | S _, [] => ([], [AuditSegReconCase 6])
  | S n, _ :: rest => let '(later, events) := audit_seg_skipn n rest in
    (later, AuditSegReconCase 7 :: events)
  end.

Fixpoint audit_seg_forward_fold {S O N E U C} (EU : encoding U) (gk : genkill_view S O N E U C)
    (u : U) (edges : list E) (initial : bool) : bool * list (audit_seg_reconstruct_call N E U) :=
  match edges with
  | [] => (initial, [AuditSegReconCase 8])
  | e :: rest => let '(next, here) := audit_seg_strict_transfer EU gk u e initial in
    let '(result, later) := audit_seg_forward_fold EU gk u rest next in
    (result, AuditSegReconCase 9 :: map AuditSegReconTransfer here ++ later)
  end.

Fixpoint audit_seg_backward_fold {S O N E U C} (EU : encoding U) (gk : genkill_view S O N E U C)
    (u : U) (edges : list E) (initial : bool) : bool * list (audit_seg_reconstruct_call N E U) :=
  match edges with
  | [] => (initial, [AuditSegReconCase 10])
  | e :: rest => let '(middle, later) := audit_seg_backward_fold EU gk u rest initial in
    let '(result, here) := audit_seg_strict_transfer EU gk u e middle in
    (result, AuditSegReconCase 11 :: later ++ map AuditSegReconTransfer here)
  end.

Definition audit_seg_recon_probe {S O N E U C} (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (gk : genkill_view S O N E U C) (u : U) (idx : seg_index N E)
    (cut : N -> bool) (cuts : FinSet.t N) (forward : bool) (n : N)
    : bool * list (audit_seg_reconstruct_call N E U) :=
  let is_cut := FinSet.mem EN n cuts in
  if is_cut then let answer := cut n in
    (answer, [AuditSegReconMem n cuts is_cut; AuditSegReconCase 12; AuditSegReconCut n answer])
  else let interior := Map.get EN n (seg_interiors idx) in
    match interior with
    | None => (false, [AuditSegReconMem n cuts is_cut; AuditSegReconCase 13;
      AuditSegReconInterior n (seg_interiors idx) interior; AuditSegReconCase 14])
    | Some (a, k) =>
      if forward then
        let found := Map.get EE a (seg_paths idx) in let path := match found with
        Some es => es
        | None => []
        end in
        let '(prefix, slice_events) := audit_seg_firstn (Nat.succ k) path in
        let source := Graph.source (seg_graph idx) a in let start := cut source in
        let '(answer, transfer_events) := audit_seg_forward_fold EU gk u prefix start in
        (answer, [AuditSegReconMem n cuts is_cut; AuditSegReconCase 13;
          AuditSegReconInterior n (seg_interiors idx) interior; AuditSegReconCase 15;
          AuditSegReconPath a (seg_paths idx) found] ++ slice_events ++
          [AuditSegReconSource a source; AuditSegReconCut source start] ++ transfer_events)
      else let target := Graph.target (seg_graph idx) a in let start := cut target in
        let found := Map.get EE a (seg_paths idx) in let path := match found with
        Some es => es
        | None => []
        end in
        let '(suffix, slice_events) := audit_seg_skipn (Nat.succ k) path in
        let '(answer, transfer_events) := audit_seg_backward_fold EU gk u suffix start in
        (answer, [AuditSegReconMem n cuts is_cut; AuditSegReconCase 13;
          AuditSegReconInterior n (seg_interiors idx) interior; AuditSegReconCase 16;
          AuditSegReconTarget a target; AuditSegReconCut target start;
          AuditSegReconPath a (seg_paths idx) found] ++ slice_events ++ transfer_events)
    end.

Definition audit_seg_recon_counted {S O N E U C} (EN : encoding N) (EE : encoding E)
    (EU : encoding U)
    (gk : genkill_view S O N E U C) (u : U) (idx : seg_index N E) (cut : N -> bool) (forward : bool)
    (n : N)
    : bool * list (audit_seg_reconstruct_call N E U) :=
  let '(cuts, setup) := audit_seg_recon_setup EN (Graph.nodes (seg_graph idx)) FinSet.empty in
  let '(result, events) := audit_seg_recon_probe EN EE EU gk u idx cut cuts forward n in
  (result, setup ++ events).

Definition audit_seg_recon_event_work {N E U} (EN : encoding N) (EE : encoding E)
    (event : audit_seg_reconstruct_call N E U) : nat :=
  64 + match event with
  | AuditSegReconAdd n _ => audit_encoding_weight (audit_key_bits_weight (encode EN n)) +
    audit_set_weight (encode EN n)
  | AuditSegReconMem n _ _ | AuditSegReconInterior n _ _ =>
    audit_encoding_weight (audit_key_bits_weight (encode EN n)) + audit_get_weight (encode EN n)
  | AuditSegReconPath e _ _ => audit_encoding_weight (audit_key_bits_weight (encode EE e)) +
    audit_get_weight (encode EE e)
  | AuditSegReconTransfer inner => audit_seg_model_event inner
  | _ => 0
  end.

Definition audit_seg_recon_work {N E U} (EN : encoding N) (EE : encoding E)
    (events : list (audit_seg_reconstruct_call N E U)) : nat :=
  256 * S (length events) * S (length events) +
    fold_right (fun event n => audit_seg_recon_event_work EN EE event + n) 0 events.

Definition audit_seg_recon_path {N E} (EN : encoding N) (EE : encoding E) (idx : seg_index N E)
    (n : N) : list E :=
  match Map.get EN n (seg_interiors idx) with
  Some (a, _) => seg_path EE idx a
  | None => []
  end.

Definition audit_seg_recon_event_bound {S O N E U C} (EN : encoding N) (EE : encoding E)
    (gk : genkill_view S O N E U C) (idx : seg_index N E) (n : N) : nat :=
  let path := audit_seg_recon_path EN EE idx n in
  32 + 4 * length (Graph.nodes (seg_graph idx)) +
    fold_right (fun e total => 16 + 3 * length (gen gk e) + total) 0 path.

Definition audit_seg_recon_width {S O N E U C} (EN : encoding N) (EE : encoding E) (EU : encoding U)
    (gk : genkill_view S O N E U C) (u : U) (idx : seg_index N E) (n : N) : nat :=
  let path := audit_seg_recon_path EN EE idx n in
  let node_width := fold_right Nat.max (audit_key_bits_weight (encode EN n))
    (map (fun v => audit_key_bits_weight (encode EN v)) (Graph.nodes (seg_graph idx))) in
  let edge_width := fold_right Nat.max 0 (map (fun e => audit_key_bits_weight (encode EE e)) path)
    in
  let expression_width := fold_right Nat.max (audit_key_bits_weight (encode EU u))
    (map (fun v => audit_key_bits_weight (encode EU v)) (flat_map (gen gk) path)) in
  let interior_width := match Map.get EN n (seg_interiors idx) with
  | Some (a, _) => audit_key_bits_weight (encode EE a)
  | None => 0
  end in
  Nat.max node_width (Nat.max edge_width (Nat.max expression_width interior_width)).

Definition audit_seg_recon_budget {S O N E U C} (EN : encoding N) (EE : encoding E)
    (EU : encoding U)
    (gk : genkill_view S O N E U C) (u : U) (idx : seg_index N E) (n : N) : nat :=
  let count := audit_seg_recon_event_bound EN EE gk idx n in
  let width := audit_seg_recon_width EN EE EU gk u idx n in
  512 * Nat.succ count * Nat.succ count + count * (128 + 6 * width).

(** Directional reconstruction returns the original answer within its event and work bounds. *)
Definition audit_seg_recon_statement : Prop :=
  forall S O N E U C (EN : encoding N) (EE : encoding E) (EU : encoding U)
      (gk : genkill_view S O N E U C) u idx cut forward n,
    let '(result, events) := audit_seg_recon_counted EN EE EU gk u idx cut forward n in
    result = (if forward then seg_reconstruct_available EN EE idx (seg_bit_transfer EU gk u) cut n
      else seg_reconstruct_busy EN EE idx (seg_bit_transfer EU gk u) cut n) /\
      length events <= audit_seg_recon_event_bound EN EE gk idx n /\
      audit_seg_recon_work EN EE events <= audit_seg_recon_budget EN EE EU gk u idx n.
