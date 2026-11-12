(** * Control-flow graph helpers *)
From Stdlib Require Import List.
From Galois.Program Require Import CfgSig.
Import List.ListNotations.

Fixpoint occurrences {E} (es : list E) (i : nat) : list (E * nat) :=
  match es with
  | [] => []
  | e :: rest => (e, i) :: occurrences rest (S i)
  end.
