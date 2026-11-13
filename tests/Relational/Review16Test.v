(** * Relational representation observations

    These examples inspect row and raw-code entry counts without invoking widening placeholders.
    For example, two stored equality rows contribute two rank units.
    Builds on: Linearize, LinCert, Karr, Poly, Zone and Octagon. *)

From Stdlib Require Import List ZArith.
From Galois.Base Require Import Key Map Trie.
From Galois.Domains Require Import ZLang.
From Galois.States Require Import EnvSig.
From Galois.Relational Require Import LinForm Linearize LinCert Karr Poly Zone Octagon Keys.
Import List.ListNotations.

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

Definition row := LCons positive [(1%positive, 1%Z)] REq 0%Z.

(** Raw row multiplicity contributes to both equality and polyhedral ranks. *)
Example repeated_rows_rank :
  Equalities.wrank 0 (Reached [row; row]) = 2%nat /\
  Polyhedra.wrank tt (Reached [row; row]) = 2%nat.
Proof.
  vm_compute. split; reflexivity.
Qed.

(** Dropping raw zone entries decreases rank even when stored row labels repeat. *)
Example zone_raw_codes_widen :
  let r := PTrieCode.set 4%positive (None, 7%Z) PTrieCode.empty in
  let m := PTrieCode.set 2%positive (None, r)
    (PTrieCode.set 8%positive (None, r) PTrieCode.empty) in
  let a := Reached m in
  (Zones.wrank 0 a,
   Zones.wrank 0 (Zones.widen 0 a Zones.top),
   Zones.leb a (Zones.widen 0 a Zones.top)) = (2%nat, 0%nat, true).
Proof.
  vm_compute. reflexivity.
Qed.

(** Dropping raw signed entries also counts their codes independently of labels. *)
Example octagon_raw_codes_widen :
  let label := (1%positive, true) in
  let r := PTrieCode.set 4%positive (label, 7%Z) PTrieCode.empty in
  let m := PTrieCode.set 2%positive (label, r)
    (PTrieCode.set 8%positive (label, r) PTrieCode.empty) in
  let a := Reached m in
  (Octagons.wrank 0 a,
   Octagons.wrank 0 (Octagons.widen 0 a Octagons.top),
   Octagons.leb a (Octagons.widen 0 a Octagons.top)) = (2%nat, 0%nat, true).
Proof.
  vm_compute. reflexivity.
Qed.

(** An empty stored zone row has no rank unit and stable widening retains it exactly. *)
Example zone_empty_row_stable :
  let a := Reached (ZoneMap.set (Some 1%positive) ZoneMap.empty ZoneMap.empty) in
  Zones.wrank 0 a = 0%nat /\ Zones.leb Zones.top a = true /\
  Zones.widen 0 a Zones.top = a.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** An empty stored signed row is likewise stable without normalizing its representation. *)
Example octagon_empty_row_stable :
  let a := Reached (OctMap.set (1%positive, true) OctMap.empty OctMap.empty) in
  Octagons.wrank 0 a = 0%nat /\ Octagons.leb Octagons.top a = true /\
  Octagons.widen 0 a Octagons.top = a.
Proof.
  vm_compute. repeat split; reflexivity.
Qed.

(** Zone rank counts entries even when raw stored labels repeat at different codes. *)
Example zone_raw_codes_rank :
  let r := PTrieCode.set 4%positive (None, 7%Z) PTrieCode.empty in
  let m := PTrieCode.set 2%positive (None, r)
    (PTrieCode.set 8%positive (None, r) PTrieCode.empty) in
  Zones.wrank 0 (Reached m) = 2%nat.
Proof.
  vm_compute. reflexivity.
Qed.

(** Octagon rank counts entries at raw codes independently of their stored literal labels. *)
Example octagon_raw_codes_rank :
  let label := (1%positive, true) in
  let r := PTrieCode.set 4%positive (label, 7%Z) PTrieCode.empty in
  let m := PTrieCode.set 2%positive (label, r)
    (PTrieCode.set 8%positive (label, r) PTrieCode.empty) in
  Octagons.wrank 0 (Reached m) = 2%nat.
Proof.
  vm_compute. reflexivity.
Qed.
