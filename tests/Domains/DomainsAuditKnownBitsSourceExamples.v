(** * Finite plain-body and selective-call observations

    These examples distinguish erased public computation from diagnostic logging.
    For example, a nonconstant left multiplier skips the second constant probe.
    Builds on: the canonical numeric source and plain operation modules. *)

From Stdlib Require Import List NArith PArith ZArith.
From Galois.Collections Require Import CollectionsEncoding CollectionsMap CollectionsFinSet
  CollectionsAuditCost.
From Galois.Bits Require Import BitsWord BitsOp.
From Galois.Domains Require Import DomainsKnownBits DomainsAuditNumericCost
  DomainsAuditKnownBitsSource.
Import List.ListNotations.

(** A nonconstant left multiplier skips the right optional-constant probe. *)
Example classic_mul_selects_constant_probe :
  length (filter (fun e => match e with AuditConstruct 502 _ => true | _ => false end)
    (snd (kb_classic_mul 2%positive (Tnum 0 0) (Tnum 3 0)))) = 1%nat.
Proof.
  vm_compute. reflexivity.
Qed.

(** Equality also skips the second probe when the first candidate is nonconstant. *)
Example classic_equal_selects_constant_probe :
  length (filter (fun e => match e with AuditConstruct 502 _ => true | _ => false end)
    (snd (kb_equal 2%positive (Tnum 0 0) (Tnum 3 0)))) = 1%nat.
Proof.
  vm_compute. reflexivity.
Qed.

(** A nonempty constant addition computes its wrapped result. *)
Example forward_add_constants :
  fst (kb_forward_source bvadd [(2%positive, Tnum 2 1); (2%positive, Tnum 1 2)]
    2%positive) = Tnum 0 3.
Proof.
  vm_compute. reflexivity.
Qed.

(** An empty operand produces bottom even when a later operand is present. *)
Example forward_empty_operand :
  fst (kb_forward_source bvadd [(2%positive, Tnum 3 3); (2%positive, Tnum 2 1)]
    2%positive) = Tnum 3 3.
Proof.
  vm_compute. reflexivity.
Qed.

(** A malformed argument list falls back to the top result. *)
Example forward_malformed_arguments :
  fst (kb_forward_source bvadd [(2%positive, Tnum 2 1)] 2%positive) = Tnum 0 0.
Proof.
  vm_compute. reflexivity.
Qed.

(** Empty scans return false and the strict scan observes both nonempty entries. *)
Example scan_empty_and_pair :
  fst (kb_any_empty_source []) = false /\
  audit_case_count 500
    (snd (kb_any_empty_source [(2%positive, Tnum 3 3); (2%positive, Tnum 2 1)])) = 3%nat.
Proof.
  vm_compute. split; reflexivity.
Qed.

(** The width-one wrap observes its boundary at two. *)
Example wrap_width_one_boundary :
  fst (domain_wrap 1%positive 2) = 0%Z.
Proof.
  vm_compute. reflexivity.
Qed.
