(** * Reverse postorder scheduler examples

    These checks observe position assignments, query defaults and their encoding receipts.
    For example, a missing vertex receives the first priority.
    Builds on: FixpointAuditScheduleAdequacy and counted natural-number encoding. *)

From Stdlib Require Import List PArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditEncoding CollectionsAuditMap.
From Galois.Fixpoint Require Import FixpointSchedule FixpointAuditSchedule
  FixpointAuditScheduleAdequacy.
Import List.ListNotations.

(** * Positions and query branches *)

(** Duplicate vertices preserve the first assigned priority. *)
Example audit_schedule_duplicate_positions :
  let positions := fst (audit_rpo_schedule_positions audit_nat_encode [1; 0; 1] 1) in
  (fst (audit_rpo_schedule_priority audit_nat_encode positions 1),
   fst (audit_rpo_schedule_priority audit_nat_encode positions 0),
   fst (audit_rpo_schedule_priority audit_nat_encode positions 2)) =
    (1%positive, 2%positive, 1%positive).
Proof.
  vm_compute; reflexivity.
Qed.

(** Membership queries distinguish an inserted widening point from a missing point. *)
Example audit_schedule_widening_branches :
  let heads := FinSet.of_list nat_encoding [1] in
  (fst (audit_rpo_schedule_widening audit_nat_encode heads 1),
   fst (audit_rpo_schedule_widening audit_nat_encode heads 0)) = (true, false).
Proof.
  vm_compute; reflexivity.
Qed.

(** A nonempty position traversal captures the actual natural encoder frames. *)
Example audit_schedule_encoding_receipt :
  let events := snd (audit_rpo_schedule_positions audit_nat_encode [1] 1) in
  existsb (fun event =>
    match event with
    | RpoScheduleMap (AuditMapSet _ _ _ _ _ body _) =>
      Nat.eqb (length body) (length (snd (audit_nat_encode 1)))
    | _ => false
    end) events = true.
Proof.
  vm_compute; reflexivity.
Qed.
