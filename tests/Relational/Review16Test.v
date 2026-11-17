(** * Relational representation observations

    These examples inspect row and raw-code entry counts without invoking widening placeholders.
    For example, two stored equality rows contribute two rank units.
    The groups are:
    - Ranks, which count stored rows and raw entries.
    - Widening, which checks widening and stability of raw and empty stored entries.
    Builds on: Linearize, LinCert, Karr, Poly, Zone and Octagon. *)

From Stdlib Require Import List ZArith.
From Galois.Base Require Import Key Map Trie.
From Galois.Domains Require Import ZLang.
From Galois.States Require Import EnvSig.
From Galois.Relational Require Import LinForm Linearize LinCert Karr Poly Zone Octagon Keys.
Import List.ListNotations.

(** * Fixtures *)

Module Numeric.
  Definition num (z : Z) := z.
End Numeric.
Module Forms := Linearize PosKey ZLang Numeric.
Module Certificates := LinCert PosKey.
Module Equalities := Karr PosKey ZLang Numeric Forms Certificates.
Module Polyhedra := Poly PosKey ZLang Numeric Forms Certificates.
Module ZoneKey := OptionKey PosKey.
Module ZoneMap := TrieMap ZoneKey.
Module Zones := Zone PosKey ZoneKey ZoneMap ZLang Numeric Forms.
Module OctKey := PairKey PosKey BoolKey.
Module OctMap := TrieMap OctKey.
Module Octagons := Octagon PosKey OctKey OctMap ZLang Numeric Forms.

(** A raw zone state whose two rows reuse the same raw entry, with no label on it. *)
Definition raw_zone_state : Zones.t :=
  Reached (PTrieCode.set 2%positive
    (None, PTrieCode.set 4%positive (None, 7%Z) PTrieCode.empty)
    (PTrieCode.set 8%positive
      (None, PTrieCode.set 4%positive (None, 7%Z) PTrieCode.empty)
      PTrieCode.empty)).

(** A raw octagon state whose two rows reuse the same raw entry under the label (1, true). *)
Definition raw_octagon_state : Octagons.t :=
  Reached (PTrieCode.set 2%positive
    ((1%positive, true), PTrieCode.set 4%positive ((1%positive, true), 7%Z) PTrieCode.empty)
    (PTrieCode.set 8%positive
      ((1%positive, true), PTrieCode.set 4%positive ((1%positive, true), 7%Z) PTrieCode.empty)
      PTrieCode.empty)).

(** * Ranks *)

Module RankTests.

  (** The unit row x = 0, used as the stored row of the rank examples. *)
  Definition row := LCons positive [(1%positive, 1%Z)] REq 0%Z.

  (** Two copies of one equality row contribute two rank units to the equality domain. *)
  Example equality_rank_counts_repeated_rows :
    Equalities.wrank 0 (Reached [row; row]) = 2%nat.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Two copies of one equality row contribute two rank units to the polyhedral domain. *)
  Example polyhedral_rank_counts_repeated_rows :
    Polyhedra.wrank tt (Reached [row; row]) = 2%nat.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A zone rank counts its entries at their raw codes, even when the stored labels repeat. *)
  Example zone_rank_counts_raw_entries :
    Zones.wrank 0 raw_zone_state = 2%nat.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An octagon rank counts its entries at their raw codes, even when the stored labels repeat. *)
  Example octagon_rank_counts_raw_entries :
    Octagons.wrank 0 raw_octagon_state = 2%nat.
  Proof.
    vm_compute. reflexivity.
  Qed.

End RankTests.

(** * Widening *)

Module WideningTests.

  (** The raw zone state starts with the rank of its two raw entries. *)
  Example zone_widening_starts_from_two_entries :
    Zones.wrank 0 raw_zone_state = 2%nat.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Widening the raw zone state against top drops its raw entries. *)
  Example zone_widening_drops_raw_entries :
    Zones.wrank 0 (Zones.widen 0 raw_zone_state Zones.top) = 0%nat.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The raw zone state stays below its widening against top. *)
  Example zone_raw_state_is_below_its_widening :
    Zones.leb raw_zone_state (Zones.widen 0 raw_zone_state Zones.top) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The raw octagon state starts with the rank of its two raw entries. *)
  Example octagon_widening_starts_from_two_entries :
    Octagons.wrank 0 raw_octagon_state = 2%nat.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Widening the raw octagon state against top drops its raw entries. *)
  Example octagon_widening_drops_raw_entries :
    Octagons.wrank 0 (Octagons.widen 0 raw_octagon_state Octagons.top) = 0%nat.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The raw octagon state stays below its widening against top. *)
  Example octagon_raw_state_is_below_its_widening :
    Octagons.leb raw_octagon_state (Octagons.widen 0 raw_octagon_state Octagons.top) = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A zone whose only stored row (for x = 1) is empty. *)
  Definition empty_zone_state : Zones.t :=
    Reached (ZoneMap.set (Some 1%positive) ZoneMap.empty ZoneMap.empty).

  (** An empty stored zone row adds no rank unit. *)
  Example empty_zone_row_has_no_rank :
    Zones.wrank 0 empty_zone_state = 0%nat.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The unconstrained zone lies below a state whose only row is empty. *)
  Example top_zone_is_below_empty_zone_row :
    Zones.leb Zones.top empty_zone_state = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Widening keeps an empty stored zone row unchanged. *)
  Example empty_zone_row_survives_widening :
    Zones.widen 0 empty_zone_state Zones.top = empty_zone_state.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** An octagon whose only stored row (for x) is empty. *)
  Definition empty_octagon_state : Octagons.t :=
    Reached (OctMap.set (1%positive, true) OctMap.empty OctMap.empty).

  (** An empty stored octagon row adds no rank unit. *)
  Example empty_octagon_row_has_no_rank :
    Octagons.wrank 0 empty_octagon_state = 0%nat.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The unconstrained octagon lies below a state whose only row is empty. *)
  Example top_octagon_is_below_empty_octagon_row :
    Octagons.leb Octagons.top empty_octagon_state = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Widening keeps an empty stored octagon row unchanged. *)
  Example empty_octagon_row_survives_widening :
    Octagons.widen 0 empty_octagon_state Octagons.top = empty_octagon_state.
  Proof.
    vm_compute. reflexivity.
  Qed.

End WideningTests.
