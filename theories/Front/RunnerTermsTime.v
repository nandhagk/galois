(** * Time of adding terms

    The third part of the timed runner. Adding a well-sorted term to a database that is loaded
    with the planned program allocates one constructor row for each application. Each
    allocation pays the amortized budget of the database at the unit bound and the identifier
    width of the result, and the potential that it leaves pays for the deferred rebuild.
    For example, adding [Add (Num 1) (Num 2)] pays for three allocations, of arities two, one
    and one.

    Builds on: the runner signature, the first two parts of the timed runner, and the time
    contracts of the database. *)

From Stdlib Require Import List PArith NArith.
From Argent Require Import Time Tactics Std Complexity.
From Galois.Egglog Require Import ValueSig Syntax Model Sorts IndexSig JoinSig DatabaseSig RunSig.
From Galois.Front Require Import Spec LowerSig RunnerSig RunnerQueryTime.

Import List.ListNotations.
Import ComplexityNotations.

Module RunnerTermsT (V : VALUE_T) (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I)
    (R : RUN_T V I J D).
  Include RunnerQueryT V I J D R.
  Definition c_terms : N := 1. (* STUB *)

  (* STUB: induction on the terms with [D.unit_mono_make]. Each make keeps the database well
     formed by [D.wf_make], with the slots of the plan from [R.check_plan_slots] and the arity
     that [term_ok] checks. *)
  Lemma add_terms_unit : forall (s : spec V.t) es db,
    spec_ok s = true -> D.wf db -> R.loaded (spec_program s) (R.plan (spec_program s)) db ->
    forallb (term_ok s) es = true -> D.unit db <= D.unit (snd (add_terms es db)).
  Proof.
  Admitted. (* STUB *)

  (* STUB: the same induction, with [D.layout_make], which allocates the identifier of each
     constructor, and [D.make_spec], which keeps every identifier allocated. *)
  Lemma add_terms_allocated : forall (s : spec V.t) es db i,
    spec_ok s = true -> D.wf db -> R.loaded (spec_program s) (R.plan (spec_program s)) db ->
    forallb (term_ok s) es = true -> In (Id i) (fst (add_terms es db)) ->
    D.allocated (snd (add_terms es db)) i.
  Proof.
  Admitted. (* STUB *)

  (* STUB: one nested induction on the term proves this lemma and [T_add_terms_amort]. Each
     constructor meets [D.T_make_amort]. The identifier count only grows, by [D.make_spec] on
     the constructor tables that [R.loaded] declares, and [D.unit_mono_make] keeps every unit
     below [U]. [c_terms] must be at least [2 * D.c_db] plus the overheads of the derived time
     functions. *)
  Lemma T_add_term_amort : forall B U (s : spec V.t) e db,
    spec_ok s = true -> D.wf db -> R.loaded (spec_program s) (R.plan (spec_program s)) db ->
    term_ok s e = true ->
    (D.ids (snd (add_term e db)) <= B)%N -> D.unit (snd (add_term e db)) <= U ->
    (T_add_term e db + N.of_nat U * D.potential B (snd (add_term e db)) <=
      N.of_nat U * (c_terms * N.of_nat (N.to_nat (N.log2 B) + 1) *
        N.of_nat (length (Syntax.slots V.t (R.plan (spec_program s))) + 1) *
        N.of_nat (term_work e) + D.potential B db))%N.
  Proof.
  Admitted. (* STUB *)

  Lemma T_add_terms_amort : forall B U (s : spec V.t) es db,
    spec_ok s = true -> D.wf db -> R.loaded (spec_program s) (R.plan (spec_program s)) db ->
    forallb (term_ok s) es = true ->
    (D.ids (snd (add_terms es db)) <= B)%N -> D.unit (snd (add_terms es db)) <= U ->
    (T_add_terms es db + N.of_nat U * D.potential B (snd (add_terms es db)) <=
      N.of_nat U * (c_terms * N.of_nat (N.to_nat (N.log2 B) + 1) *
        N.of_nat (length (Syntax.slots V.t (R.plan (spec_program s))) + 1) *
        N.of_nat (terms_work es + 1) + D.potential B db))%N.
  Proof.
  Admitted. (* STUB *)

  Lemma add_term_complexity :
    T_add_term e db ∈
      𝑂(N.of_nat (U * (N.to_nat (N.log2 B) + 1) *
        (length (Syntax.slots V.t (R.plan (spec_program s))) + 1) * term_work e))
      amortised N.of_nat U * D.potential B db ↦ N.of_nat U * D.potential B (snd (add_term e db))
      for (B, U, s, e, db) |
        spec_ok s = true /\ D.wf db /\ R.loaded (spec_program s) (R.plan (spec_program s)) db /\
        term_ok s e = true /\ (D.ids (snd (add_term e db)) <= B)%N /\
        D.unit (snd (add_term e db)) <= U.
  Proof.
  Admitted. (* STUB *)

  Lemma add_terms_complexity :
    T_add_terms es db ∈
      𝑂(N.of_nat (U * (N.to_nat (N.log2 B) + 1) *
        (length (Syntax.slots V.t (R.plan (spec_program s))) + 1) * terms_work es))
      amortised N.of_nat U * D.potential B db ↦
        N.of_nat U * D.potential B (snd (add_terms es db))
      for (B, U, s, es, db) |
        spec_ok s = true /\ D.wf db /\ R.loaded (spec_program s) (R.plan (spec_program s)) db /\
        forallb (term_ok s) es = true /\ (D.ids (snd (add_terms es db)) <= B)%N /\
        D.unit (snd (add_terms es db)) <= U.
  Proof.
  Admitted. (* STUB *)
End RunnerTermsT.
