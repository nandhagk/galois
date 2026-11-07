(** * Interface-level map, set and option automation

    These tactics rewrite public observations and expose the resulting logical cases.
    For example, [simpl_map] reduces lookup after a replacement to a key equality test.
    Builds on: BaseMap, BaseSet and BaseKeyTactics. *)

From Stdlib Require Import List Bool.
From Galois.Base Require Import BaseEncoding BaseEq BaseKeyTactics BaseMap BaseSet.
Export (hints) Map FinSet.

(** Rewrite map observations and split one reflected key test when a matching law is present. *)
Ltac simpl_map :=
  autorewrite with galois_map in *;
  try case_key;
  autorewrite with galois_map in *;
  try congruence.

(** Rewrite set observations and expose the boolean connectives of membership. *)
Ltac simpl_set :=
  autorewrite with galois_map in *;
  try case_key;
  cbn [orb andb negb] in *;
  try congruence.

(** Reflect set membership to propositional connectives and use bounded propositional search. *)
Ltac set_solver :=
  simpl_set;
  repeat rewrite ?andb_true_iff, ?orb_true_iff, ?negb_true_iff,
    <- ?not_true_iff_false in *;
  repeat match goal with
  | HE : encoding_laws ?E |- _ =>
    progress rewrite <- (FinSet.elements_spec E HE) in *
      by solve [auto using FinSet.wf_empty, FinSet.wf_add, FinSet.wf_remove,
        FinSet.wf_union, FinSet.wf_inter, FinSet.wf_diff, FinSet.wf_of_list]
  end;
  try (firstorder (auto 4)).

(** Invert option-producing matches, substitute option variables and reject constructor clashes. *)
Ltac inv_option :=
  repeat match goal with
  | H : Some _ = None |- _ => discriminate H
  | H : None = Some _ |- _ => discriminate H
  | H : Some _ = Some _ |- _ => injection H; clear H; intros; subst
  | H : context [match ?e with Some _ => _ | None => _ end] |- _ =>
    let Hoption := fresh "Hoption" in destruct e eqn:Hoption; cbn in H
  | H : ?e = Some _ |- _ => first [is_var e; subst e | progress rewrite H in *]
  | H : ?e = None |- _ => first [is_var e; subst e | progress rewrite H in *]
  end.
