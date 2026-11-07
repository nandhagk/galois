(** * Signed-bound hemisphere observations

    Queries return normalized masks and attained extrema for one sign hemisphere.
    For example, the negative query of the singleton four at width four returns no values.
    Builds on: DomainsSignedBounds. *)

From Stdlib Require Import ZArith Bool.
From Galois.Cost Require Import CostMonad.
From Galois.Bits Require Import BitsWord.
From Galois.Domains Require Import DomainsTnum DomainsSignedBounds.
Import Cost.Notations.

Local Open Scope Z_scope.

(** Queries retain the complete cost of reducing their selected hemisphere. *)
Definition signed_bounds_query_c (w : width) (a : signed_bounds) (s : bool)
    : Cost.t (option (tnum * Z * Z)) :=
  let* h := sb_reduce_half_c w s (if s then sb_one a else sb_zero a) in
  Cost.ret
    (match h with
    | SBEmpty => None
    | SBRange t lo hi => Some (t, lo, hi)
    end).

Definition signed_bounds_query (w : width) (a : signed_bounds) (s : bool)
    : option (tnum * Z * Z) :=
  Cost.value (signed_bounds_query_c w a s).

(** The pure observation reads the exact reduced hemisphere. *)
Theorem signed_bounds_query_equation : forall w a s,
  signed_bounds_query w a s =
  match sb_reduce_half w s (if s then sb_one a else sb_zero a) with
  | SBEmpty => None
  | SBRange t lo hi => Some (t, lo, hi)
  end.
Proof.
  intros w a s. unfold signed_bounds_query, signed_bounds_query_c.
  autorewrite with galois_cost. reflexivity.
Qed.

(** Every feasible original word satisfies the queried mask and inclusive endpoints. *)
Theorem signed_bounds_query_sound : forall w a s t lo hi z,
  signed_bounds_query w a s = Some (t, lo, hi) ->
  sb_half_gamma w s (if s then sb_one a else sb_zero a) z ->
  tnum_gamma w t z /\ lo <= z <= hi.
Proof.
  intros w a s t lo hi z Hquery Hz. rewrite signed_bounds_query_equation in Hquery.
  pose proof (proj2 (sb_reduce_half_gamma w s _ z) Hz) as Hreduced.
  destruct (sb_reduce_half w s (if s then sb_one a else sb_zero a)) as [|t' lo' hi'];
    [discriminate|]. injection Hquery as <- <- <-.
  apply sb_half_gamma_range in Hreduced. tauto.
Qed.

(** Query failure is equivalent to emptiness of the original selected hemisphere. *)
Theorem signed_bounds_query_empty : forall w a s,
  signed_bounds_query w a s = None <->
  forall z, ~ sb_half_gamma w s (if s then sb_one a else sb_zero a) z.
Proof.
  intros w a s. rewrite signed_bounds_query_equation.
  pose proof (sb_reduce_half_summary w s (if s then sb_one a else sb_zero a)) as Hsummary.
  destruct (sb_reduce_half w s (if s then sb_one a else sb_zero a)) as [|t lo hi].
  - split; [intro Hquery; exact Hsummary|intro Hempty; reflexivity].
  - split; [discriminate|]. intro Hempty.
    destruct Hsummary as [_ [Hlo _]]. exfalso. exact (Hempty lo Hlo).
Qed.

(** Both reported endpoints are feasible original words in the selected hemisphere. *)
Theorem signed_bounds_query_bounds_exact : forall w a s t lo hi,
  signed_bounds_query w a s = Some (t, lo, hi) ->
  sb_half_gamma w s (if s then sb_one a else sb_zero a) lo /\
  sb_half_gamma w s (if s then sb_one a else sb_zero a) hi.
Proof.
  intros w a s t lo hi Hquery. rewrite signed_bounds_query_equation in Hquery.
  pose proof (sb_reduce_half_summary w s (if s then sb_one a else sb_zero a)) as Hsummary.
  destruct (sb_reduce_half w s (if s then sb_one a else sb_zero a)) as [|t' lo' hi'];
    [discriminate|]. injection Hquery as <- <- <-.
  destruct Hsummary as [_ [Hlo [Hhi _]]]. now split.
Qed.
