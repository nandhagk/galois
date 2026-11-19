(** * Closed views of specifications that read lattice tables

    A view that the rules of a monotone specification close holds the meaning of the
    specification over its own rows. [lat_least] reduces this to one clause at a time, with
    reads that see values below the stored values. The plan [LATTICE_READ_RAISE_PLAN] raises the
    read values to the stored values, the plan [LATTICE_READ_QUERY_PLAN] then matches the query
    of the rule, and the closed view holds its put. For an assigned value, [monotone] puts the
    raised value above the assigned one, and the put stores a value above the raised one.

    For example, in a closed view of the shortest-path rules the distance stored at [[a; c]] is
    at most [d + w] for every distance [d] stored at [[a; b]] and every edge from [b] to [c] of
    weight [w].

    Builds on: the lattice-read signature and its plans, the meaning of lattice reads and the
    lowering laws. *)

From Stdlib Require Import List PArith Bool.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts RunSig.
From Galois.Front Require Import Spec SpecLattice LowerSig RunnerSig LatticeReadSig.

Import List.ListNotations.

Module LatticeReadClosed (V : VALUE) (LW : LOWER_LAWS) (Q : LATTICE_READ_QUERY_PLAN)
    (RS : LATTICE_READ_RAISE_PLAN) <: LATTICE_READ_CLOSED_PLAN V.
  (* STUB: [lat_least] with the rows of [w] for [P] and [stored_above V.merge s w] for both [A]
     and [Q]. Two stored values at one key are equal, so [V.merge_assoc] closes [Q] under the
     merges. For a clause, [RS.body_reads_raise] and [RS.head_keys_raise] give an environment
     whose reads see the stored values. Restricted below [clause_fresh c], it matches the query
     of the rule by [Q.query_body_stored_matches] and [LW.checks_last_matches], [closed] gives
     the actions, and [Q.query_body_stored_lets] and [LW.build_pats_present_sound] reach the
     put. A derived row has no output by [RS.derive_head_rel], and an assigned value is below
     the raised value by [monotone], which is below the stored value. *)
  Lemma lower_reads_closed : forall (s : spec V.t) (w : @view V.t),
    spec_ok s = true -> lattice_reads s = true -> reads_ok s = true ->
    monotone V.prim V.merge s -> closed V.prim V.merge (spec_program s) w ->
    (forall g, kind w g = lookup_kind (tables s) g) ->
    (forall g k o, row w g k o -> lookup_kind (tables s) g = Some ORel -> o = None) ->
    (forall g k o1 o2, row w g k o1 -> row w g k o2 -> o1 = o2) ->
    (forall r vs, lat_derived V.prim V.merge s (view_rows w) r vs -> view_rows w r vs) /\
    (forall f ks u, lat_assigned V.prim V.merge s (view_rows w) f ks u ->
      stored_above V.merge s w f ks u).
  Proof.
  Admitted. (* STUB *)
End LatticeReadClosed.
