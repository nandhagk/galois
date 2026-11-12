(** * Operator case analysis

    Case analysis preserves every branch that the client's default cannot solve.
    For example, a default for bitwise operators leaves arithmetic operators visible.
    Builds on: Rocq Ltac constructor case analysis. *)

(** Clients override this hook with a tactic that solves their default operator cases. *)
Ltac op_default := fail.

(** [op_cases o] splits constructors in declaration order and removes only solved defaults.
    [op_cases o by t] uses [t] instead of the hook and leaves all unsolved goals unchanged. *)
Tactic Notation "op_cases" ident(o) := destruct o; try (solve [op_default]).
Tactic Notation "op_cases" ident(o) "by" tactic3(t) := destruct o; try (solve [t]).

(** [kind_cases k] splits a descriptor kind and removes only solved client defaults. *)
Tactic Notation "kind_cases" ident(k) := destruct k; try (solve [op_default]).
Tactic Notation "kind_cases" ident(k) "by" tactic3(t) := destruct k; try (solve [t]).
