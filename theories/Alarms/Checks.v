(** * Alarm check interfaces

    Alarm checks share the check data and interfaces exported by ChecksSig.
    For example, a check records its site and operand terms.
    Concrete bit-level checks belong to BitsChecks in D1.

    Main results
    - [may_fail_sound] A successful check excludes concrete errors.
    - [may_fail_complexity] A check is linear in its operand work.

    Builds on: ChecksSig. *)

From Galois.Alarms Require Export ChecksSig.
