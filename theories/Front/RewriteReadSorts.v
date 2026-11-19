(** * Right sides of rewrites that read rows

    The rule of a rewrite ends with a union of its two sides, and the sort check accepts a union
    only of two classes. So the right side of a rewrite of a well-sorted specification is a
    constructor pattern or a variable of a class. When every relation and every lattice table
    takes only values ([value_tables]), a premise binds no variable of a class, and such a
    variable sits at a class position of the left side. A left side that a class represents in a
    sorted view then makes the instance of the right side an application. The argument is the
    one of [RewriteSorts.v], with premises that read rows and values in place of input premises.

    For example, the instances of the rewrite [known x c -> Mul (Ref x) a => Scale c a] have the
    application [Scale c a] on the right.

    Builds on: the signature of rewrites that read rows, the meaning of equations that read
    rows, the specifications, their lowering and the sort checker. *)

From Stdlib Require Import List PArith.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts.
From Galois.Front Require Import Spec SpecReads LowerSig RunnerSig RewriteReadSig.

Import List.ListNotations.

Module RewriteReadSorts (V : VALUE) <: REWRITE_READ_SORTS_PLAN V.
  (* STUB: [check_program_spec] makes the rule of the rewrite well sorted, and its last action
     [Union] needs the term of the right side at the sort [SId]. A constructor pattern gives an
     application. A variable of sort [SId] is bound by the left side outside primitive calls,
     because [value_tables s = true] makes each premise bind only variables of values.
     [represents w (Id i) tl] in a view sorted by [view_sorted] gives each class position of the
     left side a class, which represents only applications ([rep_app]). *)
  Lemma read_right_app : forall (s : spec V.t) (P : positive -> list V.t -> Prop)
      (Q : positive -> list V.t -> V.t -> Prop) (w : @view V.t) c e l r tl tr i,
    spec_ok s = true -> value_tables s = true ->
    view_sorted (program_sorts (spec_program s)) w ->
    In c (clauses s) -> head c = Rewrites l r ->
    Forall (read_premise V.prim P Q e) (body c) ->
    pat_term V.prim e l = Some tl -> pat_term V.prim e r = Some tr ->
    represents w (Id i) tl -> exists f us, tr = EApp f us.
  Proof.
  Admitted. (* STUB *)
End RewriteReadSorts.
