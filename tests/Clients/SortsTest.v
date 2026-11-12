(** * Client program sort checks

    The sort checker accepts the pointer analysis programs.
    For example, the inclusion rules use bound value variables in their actions.
    Builds on: Egglog sorts and the pointer analysis signatures. *)

From Galois.Egglog Require Import Sorts.
From Galois.Clients Require Import AndersenSig SteensgaardSig.

(** The inclusion analysis program is well sorted. *)
Example andersen_program_sorted : check_program andersen_program = true.
Proof.
  vm_compute. reflexivity.
Qed.

(** The unification analysis program is well sorted. *)
Example steensgaard_program_sorted : check_program steensgaard_program = true.
Proof.
  vm_compute. reflexivity.
Qed.
