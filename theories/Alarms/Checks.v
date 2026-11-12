(** * Alarm check interfaces

    Alarm checks share the check data and interfaces exported by ChecksSig.
    For example, a check records its site and operand terms.
    Concrete bit-level checks belong to BitsChecks in D1.
    Builds on: ChecksSig. *)

From Galois.Alarms Require Export ChecksSig.
