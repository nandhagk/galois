(** * Join syntax erasure

    Counted syntax preparation returns the original variable and atom lists.
    For example, a repeated variable remains repeated until set construction.
    Builds on: RulesAuditJoinSyntax, CollectionsAuditFinSetAdequacy,
    CollectionsAuditElementsAdequacy and CollectionsAuditUnionAdequacy. *)

From Stdlib Require Import List.
From Galois.Collections Require Import CollectionsEncoding CollectionsFinSet
  CollectionsAuditEncoding CollectionsAuditFinSet CollectionsAuditElements CollectionsAuditUnion
  CollectionsAuditEncodingAdequacy CollectionsAuditFinSetAdequacy
  CollectionsAuditElementsAdequacy CollectionsAuditUnionAdequacy.
From Galois.Rules Require Import RulesSyntax RulesCompile RulesJoin RulesAuditMaterializePrelude
  RulesAuditJoinSyntax.
Import List.ListNotations.

(** * List and set observations *)

Lemma mat_append_value A (xs ys : list A) : fst (mat_append xs ys) = xs ++ ys.
Proof.
  induction xs as [|x xs IH]; cbn [mat_append mat_mark mat_return mat_bind] in *.
  - reflexivity.
  - destruct (mat_append xs ys); cbn in *; now rewrite IH.
Qed.

Lemma mat_flatmap_value A B (f : A -> mat_run (list B)) xs :
  fst (mat_flatmap f xs) = flat_map (fun x => fst (f x)) xs.
Proof.
  induction xs as [|x xs IH]; cbn [mat_flatmap mat_mark mat_return mat_bind] in *.
  - reflexivity.
  - destruct (f x) as [first fe] eqn:Hf.
    destruct (mat_flatmap f xs) as [rest re].
    pose proof (mat_append_value B first rest) as Happ.
    destruct (mat_append first rest) as [out oe] eqn:Hout; cbn in Happ.
    cbn [mat_mark mat_bind]; rewrite Hout; cbn.
    cbn in IH; rewrite IH in Happ; rewrite Hf; exact Happ.
Qed.

Lemma mat_filter_value A (f : A -> mat_run bool) xs :
  fst (mat_filter f xs) = filter (fun x => fst (f x)) xs.
Proof.
  induction xs as [|x xs IH]; cbn [mat_filter mat_mark mat_return mat_bind] in *.
  - reflexivity.
  - destruct (f x) as [keep fe] eqn:Hf.
    destruct (mat_filter f xs) as [rest re].
    cbn in *; rewrite IH, Hf; reflexivity.
Qed.

Lemma mat_nat_set_value xs :
  fst (mat_of_list audit_nat_encode audit_nat_events_work xs) = FinSet.of_list nat_encoding xs.
Proof.
  unfold mat_of_list, mat_lift.
  pose proof (audit_finset_of_list_erases _ _ audit_nat_encode nat_encoding xs) as H.
  destruct (audit_finset_of_list audit_nat_encode xs); cbn in *.
  apply H; intros; apply audit_nat_encode_erases.
Qed.

Lemma mat_atom_vars_value P (a : atom P) : fst (mat_atom_vars a) = atom_vars a.
Proof.
  unfold mat_atom_vars, atom_vars; rewrite mat_flatmap_value.
  apply flat_map_ext; intro t; destruct t; reflexivity.
Qed.

Lemma mat_has_variable_value P v (a : atom P) :
  fst (mat_has_variable v a) =
    FinSet.mem nat_encoding v (FinSet.of_list nat_encoding (atom_vars a)).
Proof.
  unfold mat_has_variable, mat_bind.
  pose proof (mat_atom_vars_value P a) as Ha.
  destruct (mat_atom_vars a) as [variables events]; cbn in Ha; subst variables.
  pose proof (mat_nat_set_value (atom_vars a)) as Hset.
  destruct (mat_of_list audit_nat_encode audit_nat_events_work (atom_vars a))
      as [vars set_events].
  cbn in Hset; subst vars.
  unfold mat_lift.
  pose proof (audit_finset_mem_erases _ _ audit_nat_encode nat_encoding v
    (FinSet.of_list nat_encoding (atom_vars a)) (audit_nat_encode_erases v)) as Hmem.
  destruct (audit_finset_mem audit_nat_encode v (FinSet.of_list nat_encoding (atom_vars a))).
  exact Hmem.
Qed.

(** The counted syntax helpers erase to the original source operations. *)
Theorem mat_join_syntax_erasure : mat_join_syntax_erasure_statement.
Proof.
  unfold mat_join_syntax_erasure_statement.
  repeat split.
  - exact mat_atom_vars_value.
  - intros P bound a; unfold mat_bound_add, bound_add, mat_bind.
    pose proof (mat_atom_vars_value P a) as Ha.
    destruct (mat_atom_vars a) as [variables events]; cbn in Ha; subst variables.
    pose proof (mat_nat_set_value (atom_vars a)) as Hset.
    destruct (mat_of_list audit_nat_encode audit_nat_events_work (atom_vars a))
      as [vars set_events].
    cbn in Hset; subst vars.
    unfold mat_union, mat_lift.
    pose proof (audit_finset_union_erases nat nat_encoding bound
      (FinSet.of_list nat_encoding (atom_vars a))) as Hunion.
    destruct (audit_finset_union bound (FinSet.of_list nat_encoding (atom_vars a))).
    exact Hunion.
  - intros P items; unfold mat_positive_atoms, positive_atoms; rewrite mat_flatmap_value.
    apply flat_map_ext; intro item; destruct item; reflexivity.
  - intros P atoms; unfold mat_join_variables, join_variables, mat_bind.
    pose proof (mat_flatmap_value _ _ mat_atom_vars atoms) as Hvars.
    assert (Hsource : flat_map (fun a : atom P => fst (mat_atom_vars a)) atoms =
      flat_map atom_vars atoms).
    { apply flat_map_ext; apply mat_atom_vars_value. }
    rewrite Hsource in Hvars.
    destruct (mat_flatmap mat_atom_vars atoms) as [variables events]; cbn in Hvars; subst variables.
    pose proof (mat_nat_set_value (flat_map atom_vars atoms)) as Hset.
    destruct (mat_of_list audit_nat_encode audit_nat_events_work (flat_map atom_vars atoms))
      as [vars set_events]; cbn in Hset; subst vars.
    unfold mat_elements, mat_lift.
    pose proof (audit_finset_elements_erases nat (FinSet.of_list nat_encoding
      (flat_map atom_vars atoms))) as Helements.
    destruct (audit_finset_elements (FinSet.of_list nat_encoding (flat_map atom_vars atoms))).
    exact Helements.
  - intros P v atoms; unfold mat_atoms_with, atoms_with_variable; rewrite mat_filter_value.
    apply filter_ext; intro a; apply mat_has_variable_value.
Qed.
