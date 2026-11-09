(** * Empty e-graph boundaries

    Class operations reject identifiers that have no allocated node.
    For example, even a self-union of an unknown identifier is rejected.
    Builds on: EgraphGraph. *)

From Stdlib Require Import List BinPos NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseUnionFind.
From Galois.Egraph Require Import EgraphSyntax EgraphGraph EgraphSpec.
Import List.ListNotations.

Definition sample_alg : EggAlg.t nat bool nat :=
  EggAlg.of_pure (codec_enc nat_codec) (codec_enc bool_codec) (codec_enc nat_codec)
    (fun _ => Some true) (fun _ _ _ => true).

Example empty_unknown_sort :
  Egraph.sort_of sample_alg Egraph.empty 1%positive = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_unknown_self_union :
  Egraph.union sample_alg Egraph.empty 1%positive 1%positive = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_unknown_find :
  Egraph.find sample_alg Egraph.empty 1%positive = 1%positive.
Proof.
  vm_compute. reflexivity.
Qed.

(** Word sort is true, boolean sort is false, and operators are add, mul, lt, ite and f. *)
Definition arith : EggAlg.t nat bool nat :=
  EggAlg.of_pure (codec_enc nat_codec) (codec_enc bool_codec) (codec_enc nat_codec)
    (fun v => Some (negb (Nat.eqb v 0)))
    (fun op ss s =>
      match op, ss, s with
      | 0, [true; true], true => true
      | 1, [true; true], true => true
      | 2, [true; true], false => true
      | 3, [false; true; true], true => true
      | 4, [true], true => true
      | _, _, _ => false
      end).

Definition leaf_a : EggTerm.t nat bool nat := EggTerm.Var true 1.
Definition leaf_b : EggTerm.t nat bool nat := EggTerm.Var true 2.
Definition unary e : EggTerm.t nat bool nat := EggTerm.App true 4 [e].

Definition arithmetic_term : EggTerm.t nat bool nat :=
  EggTerm.App true 3
    [EggTerm.App false 2 [leaf_a; leaf_b];
      EggTerm.App true 0 [leaf_a; leaf_b];
      EggTerm.App true 1 [leaf_a; leaf_b]].

Example arithmetic_two_sort_shapes :
  option_map (fun result => (fst result, Egraph.sort_of arith (snd result) (fst result),
    Egraph.next (snd result))) (Egraph.add_term arith Egraph.empty arithmetic_term) =
    Some (6%positive, Some true, 7%positive).
Proof.
  vm_compute. reflexivity.
Qed.

Definition congruence_fixture :=
  match Egraph.add_term arith Egraph.empty (unary leaf_a) with
  | None => None
  | Some (_, g) => Egraph.add_term arith g (unary leaf_b)
  end.

Definition union_fixture :=
  match congruence_fixture with
  | None => None
  | Some (_, g) => Egraph.union arith g 1%positive 3%positive
  end.

Example add_terms_allocate_children_first :
  option_map (fun result => (fst result, Egraph.next (snd result))) congruence_fixture =
    Some (4%positive, 5%positive).
Proof.
  vm_compute. reflexivity.
Qed.

Example union_defers_congruence :
  option_map (fun g => Pos.eqb (Egraph.find arith g 2%positive)
    (Egraph.find arith g 4%positive)) union_fixture = Some false.
Proof.
  vm_compute. reflexivity.
Qed.

Example rebuild_merges_congruent_applications :
  option_map (fun g =>
    let h := Egraph.rebuild arith g in
    Pos.eqb (Egraph.find arith h 2%positive) (Egraph.find arith h 4%positive))
    union_fixture = Some true.
Proof.
  vm_compute. reflexivity.
Qed.

Definition cascade_fixture :=
  match Egraph.add_term arith Egraph.empty (unary (unary leaf_a)) with
  | None => None
  | Some (_, g) =>
    match Egraph.add_term arith g (unary (unary leaf_b)) with
    | None => None
    | Some (_, h) => Egraph.union arith h 1%positive 4%positive
    end
  end.

Example cascade_starts_with_distinct_inner_and_outer_classes :
  option_map (fun g =>
    (Pos.eqb (Egraph.find arith g 2%positive) (Egraph.find arith g 5%positive),
      Pos.eqb (Egraph.find arith g 3%positive) (Egraph.find arith g 6%positive)))
    cascade_fixture = Some (false, false).
Proof.
  vm_compute. reflexivity.
Qed.

Example rebuild_merges_inner_then_outer_congruence :
  option_map (fun g =>
    let h := Egraph.rebuild arith g in
    (Pos.eqb (Egraph.find arith h 2%positive) (Egraph.find arith h 5%positive),
      Pos.eqb (Egraph.find arith h 3%positive) (Egraph.find arith h 6%positive)))
    cascade_fixture = Some (true, true).
Proof.
  vm_compute. reflexivity.
Qed.

Example insertion_reuses_clean_node :
  option_map (fun result =>
    let g := Egraph.rebuild arith (snd result) in
    option_map (fun added =>
      (Pos.eqb (fst added) (Egraph.find arith g 2%positive),
       Egraph.next (snd added)))
      (Egraph.add_node arith g (Egraph.NApp true 4 [1%positive])))
    congruence_fixture = Some (Some (true, 5%positive)).
Proof.
  vm_compute. reflexivity.
Qed.

Example malformed_application_rejected :
  Egraph.add_node arith Egraph.empty (Egraph.NApp true 0 []) = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example missing_child_rejected :
  Egraph.add_node arith Egraph.empty (Egraph.NApp true 4 [1%positive]) = None.
Proof.
  vm_compute. reflexivity.
Qed.

Example wrong_variable_sort_rejected :
  Egraph.add_node arith Egraph.empty (Egraph.NVar true 0) = None.
Proof.
  vm_compute. reflexivity.
Qed.

Definition two_sort_fixture :=
  match Egraph.add_term arith Egraph.empty leaf_a with
  | None => None
  | Some (_, g) => Egraph.add_term arith g (EggTerm.Var false 0)
  end.

Example sort_mismatched_union_rejected :
  option_map (fun result => Egraph.union arith (snd result) 1%positive 2%positive)
    two_sort_fixture = Some None.
Proof.
  vm_compute. reflexivity.
Qed.

Example allocated_self_union_succeeds :
  option_map (fun result => option_map (fun h => Egraph.next h)
    (Egraph.union arith (snd result) 1%positive 1%positive))
    (Egraph.add_term arith Egraph.empty leaf_a) = Some (Some 2%positive).
Proof.
  vm_compute. reflexivity.
Qed.

Definition cyclic_with_leaf :=
  match Egraph.add_term arith Egraph.empty (unary leaf_a) with
  | None => None
  | Some (_, g) => Egraph.union arith g 1%positive 2%positive
  end.

Example memo_hit_can_name_a_class_with_a_different_representative_node :
  option_map (fun g => option_map
    (fun result => (fst result, Egraph.next (snd result)))
    (Egraph.add_node arith g (Egraph.NApp true 4 [1%positive])))
    cyclic_with_leaf = Some (Some (1%positive, 3%positive)).
Proof.
  vm_compute. reflexivity.
Qed.

Definition stale_key_fixture :=
  match Egraph.add_term arith Egraph.empty leaf_a with
  | None => None
  | Some (_, g) =>
    match Egraph.add_term arith g (unary leaf_b) with
    | None => None
    | Some (_, h) => Egraph.union arith h 1%positive 2%positive
    end
  end.

Example stale_signature_is_repaired_by_rebuild :
  option_map (fun g =>
    let h := Egraph.rebuild arith g in
    option_map (fun result => (fst result, Egraph.next (snd result)))
      (Egraph.add_node arith h (Egraph.NApp true 4 [2%positive])))
    stale_key_fixture = Some (Some (3%positive, 4%positive)).
Proof.
  vm_compute. reflexivity.
Qed.

Example dirty_query_miss_is_repaired_after_allocation :
  option_map (fun g => option_map (fun result =>
    let h := Egraph.rebuild arith (snd result) in
    (fst result, Egraph.next h,
      Pos.eqb (Egraph.find arith h (fst result)) (Egraph.find arith h 3%positive)))
    (Egraph.add_node arith g (Egraph.NApp true 4 [2%positive])))
    stale_key_fixture = Some (Some (4%positive, 5%positive, true)).
Proof.
  vm_compute. reflexivity.
Qed.

Example empty_rebuild_allocates_nothing :
  Egraph.next (Egraph.rebuild arith Egraph.empty) = 1%positive.
Proof.
  vm_compute. reflexivity.
Qed.

Definition many_same_op m :=
  Egraph.add_terms arith Egraph.empty
    (map (fun i => unary (EggTerm.Var true (S i))) (seq 0 m)).

Definition many_rebuild_ticks m :=
  match many_same_op m with
  | None => None
  | Some (_, g) =>
    match Egraph.union arith g 1%positive 3%positive with
    | None => None
    | Some g => Some (Cost.ticks (Egraph.rebuild_c arith g))
    end
  end.

Example many_same_op_rebuild_costs :
  (many_rebuild_ticks 4, many_rebuild_ticks 8, many_rebuild_ticks 16) =
    (Some 441%N, Some 441%N, Some 441%N).
Proof.
  vm_compute. reflexivity.
Qed.

(** This raw fixture is deliberately outside the WF domain and contains no leaf node. *)
Definition raw_no_leaf_cycle : Egraph.t nat bool nat :=
  Egraph.Make nat bool nat UnionFind.make
    (Map.set positive_encoding 1%positive (Egraph.NApp true 4 [1%positive]) Map.empty)
    Map.empty 2%positive Egraph.empty_kernel.

Example raw_no_leaf_cycle_can_be_scanned :
  let g := Egraph.rebuild arith raw_no_leaf_cycle in
  (Egraph.find arith g 1%positive, Egraph.sort_of arith g 1%positive, Egraph.next g) =
    (1%positive, Some true, 2%positive).
Proof.
  vm_compute. reflexivity.
Qed.

(** The raw no-leaf cycle has no finite representation derivation at any identifier. *)
Theorem raw_no_leaf_cycle_no_representation :
  forall c e, ~ EggSpec.represents arith raw_no_leaf_cycle c e.
Proof.
  assert (Hlookup : forall i, EggSpec.nodes_get raw_no_leaf_cycle i =
    if eqb positive_encoding i 1%positive
    then Some (Egraph.NApp true 4 [1%positive]) else None).
  { intro i.
    change (Map.get positive_encoding i
      (Map.set positive_encoding 1%positive
        (@Egraph.NApp nat bool nat true 4 [1%positive]) Map.empty) =
      if eqb positive_encoding i 1%positive
      then Some (Egraph.NApp true 4 [1%positive]) else None).
    rewrite Map.get_set by apply Map.wf_empty.
    now rewrite Map.get_empty. }
  unfold not.
  fix IH 3.
  intros c e Hrep.
  destruct Hrep as [c i s v Hsame Hnode|c i s op cs args Hsame Hnode Hargs].
  - rewrite Hlookup in Hnode.
    destruct (eqb positive_encoding i 1%positive); discriminate Hnode.
  - rewrite Hlookup in Hnode.
    destruct (eqb positive_encoding i 1%positive); [|discriminate Hnode].
    injection Hnode as Hsort Hop Hchildren; subst s op cs.
    inversion Hargs as [|d child ds children Hchild Hrest]; subst d ds.
    exact (IH 1%positive child Hchild).
Qed.

(** WF rejects the raw cycle because its allocated class has no finite witness. *)
Theorem raw_no_leaf_cycle_not_wf : ~ EggSpec.wf arith raw_no_leaf_cycle.
Proof.
  intro Hwf.
  assert (Hnode : EggSpec.nodes_get raw_no_leaf_cycle 1%positive =
    Some (Egraph.NApp true 4 [1%positive])) by (vm_compute; reflexivity).
  destruct (EggSpec.finite_witness arith raw_no_leaf_cycle Hwf 1%positive _ Hnode)
    as [e He].
  exact (raw_no_leaf_cycle_no_representation 1%positive e He).
Qed.

(** The arithmetic fixture supplies lawful operator, sort and variable encodings. *)
Theorem arith_encoding_laws : EggSpec.encoding_laws arith.
Proof.
  constructor.
  - exact nat_encoding_laws.
  - exact bool_encoding_laws.
  - exact nat_encoding_laws.
Qed.

(** Public allocation and union laws admit a productive cyclic class containing a leaf. *)
Theorem cyclic_with_leaf_wf :
  forall g, cyclic_with_leaf = Some g -> EggSpec.wf arith g.
Proof.
  intros g; unfold cyclic_with_leaf.
  destruct (Egraph.add_term arith Egraph.empty (unary leaf_a)) as [[c h]|] eqn:Hadded;
    [|discriminate].
  intro Hunion.
  destruct (proj1 (EggSpec.add_term_represents arith Egraph.empty (unary leaf_a)
    arith_encoding_laws (EggSpec.empty_wf arith)) c h Hadded) as [_ [Hwf Hext]].
  exact (EggSpec.union_wf arith h 1%positive 2%positive g arith_encoding_laws Hwf Hunion).
Qed.
