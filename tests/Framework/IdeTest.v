(** * IDE composition observations

    Matched returns compose caller, call, callee and return functions.
    For example, reversing the call and return changes the observed affine result.

    Groups:
    - Composition: a matched return gives its affine value, and the composed function applies to 4.
    - Translation: the affine rules agree with the reference, and the affine checker accepts the jump.
    - Roots: the affine rules list their seeds, roots, steps and returns.
    - Unchecked: a bad micro lattice and a flow without facts are still checked by the enumerated rows.

    Builds on: Framework.Ide and Framework.IfdsTest. *)

From Stdlib Require Import List Bool Arith ZArith.
From Galois.Base Require Import Key.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import ConstSig.
From Galois.Fixpoint Require Import Query.
From Galois.Program Require Import CfgSig IcfgSig.
From Galois.Base Require Import KeySig.
From Galois.Framework Require Import IfdsSig Ifds IdeSig Ide.
From Galois.Tests.Framework Require Import IfdsTest.
Import List.ListNotations.

(** * Fixtures *)

(** Natural numbers as a lattice of values, with 0 as bottom and max as join. *)
Module Values <: LATTICE_OPS.
  Definition t := nat.
  Definition leb := Nat.leb.
  Definition bot := 0.
  Definition is_bot n := Nat.eqb n 0.
  Definition join := Nat.max.
End Values.

(** Affine functions x |-> a * x + b, written as the pair (a, b). *)
Module Affine <: MICRO_OPS Values.
  Definition t := (nat * nat)%type.
  Definition leb (f g : t) := Nat.eqb (fst f) (fst g) && Nat.eqb (snd f) (snd g).
  Definition bot : t := (0, 0).
  Definition is_bot (f : t) := leb f bot.
  Definition join (f _ : t) := f.
  Definition identity : t := (1, 0).
  Definition compose (f g : t) := (fst f * fst g, fst f * snd g + snd f).
  Definition apply (f : t) x := fst f * x + snd f.
End Affine.

(** The flow of Ifds with the weights of the edges 0, 2 and the others. *)
Module Flow <: IDE_FLOW_OPS Prog NatKeyCode Edge Fact Values Affine.
  Definition facts := Flow.facts.
  Definition flow := Flow.flow.
  Definition seeds := Flow.seeds.
  Definition weight (_ : unit) e (_ _ : option unit) : Affine.t :=
    match e with 0 => (1, 1) | 2 => (1, 3) | _ => (1, 0) end.
End Flow.

Module A := IdeCode Prog NatKeyCode Edge Graph NatKeyCode Icfg Fact Values Affine Flow Rules.

(** Integers as a lattice of values, with 0 as bottom and max as join. *)
Module ZValues <: LATTICE_OPS.
  Definition t := Z.
  Definition leb := Z.leb.
  Definition bot := 0%Z.
  Definition is_bot n := Z.eqb n 0%Z.
  Definition join := Z.max.
End ZValues.

(** Flat translations of integers, with bottom, a value and top. *)
Module Translation <: MICRO_OPS ZValues.
  Definition t := flat Z.
  Definition leb (a b : t) := match a, b with
    | FBot, _ | _, FTop => true
    | FVal x, FVal y => Z.eqb x y
    | _, _ => false
    end.
  Definition bot : t := FBot.
  Definition is_bot (a : t) := match a with FBot => true | _ => false end.
  Definition join (a b : t) := match a, b with
    | FBot, _ => b | _, FBot => a
    | FVal x, FVal y => if Z.eqb x y then a else FTop
    | _, _ => FTop
    end.
  Definition identity : t := FVal 0%Z.
  Definition compose (a b : t) := match a, b with
    | FBot, _ | _, FBot => FBot
    | FVal x, FVal y => FVal (x + y)%Z
    | _, _ => FTop
    end.
  Definition apply (f : t) (x : Z) := match f with
    | FVal z => (x + z)%Z
    | _ => 0%Z
    end.
End Translation.

(** A flow with one fact, whose weight is 1 on edge 1 and 0 elsewhere. *)
Module AffineFlow <: IDE_FLOW_OPS Prog NatKeyCode Edge Fact ZValues Translation.
  Definition facts (_ : unit) : list (option unit) := [None].
  Definition flow (_ : unit) (_ : nat) (d : option unit) := [d].
  Definition seeds (_ : unit) : list (nat * option unit) := [(0, None)].
  Definition weight (_ : unit) e (_ _ : option unit) : Translation.t :=
    FVal (if Nat.eqb e 1 then 1%Z else 0%Z).
End AffineFlow.

(** The prepared path rules of the affine flow. *)
Definition affine_rules := Eval vm_compute in
  path_rules_fast NatKeyCode.encode (Icfg.kind tt) (Graph.dst tt) (AffineFlow.facts tt)
    (AffineFlow.flow tt) (AffineFlow.seeds tt) (Graph.edges tt).

Module AffineRules <: IFDS_RULES_OPS Prog NatKeyCode Edge Fact.
  Definition rules (_ : unit) := affine_rules.
End AffineRules.

Module ASys := IdeCode Prog NatKeyCode Edge Graph NatKeyCode Icfg Fact ZValues Translation
  AffineFlow AffineRules.

(** The lookup that gives value 0 at the first two keys and value 1 at keys 2 and 3, and bottom elsewhere. *)
Definition affine_lookup (k : ASys.key) : Translation.t :=
  match snd k with
  | (0, None) | (1, None) => FVal 0%Z
  | (2, None) | (3, None) => FVal 1%Z
  | _ => FBot
  end.

(** Whether the lookup satisfies every row of the affine system. *)
Definition affine_check lookup := forallb (fun r =>
  row_ok Translation.leb lookup (ASys.target tt r)
    (eval_query (ASys.resume tt) lookup (S (length (ASys.deps tt r))) (ASys.start tt r)))
  (ASys.rows tt).

(** * Composition *)

Module CompositionTests.

  (** The matched return through the call and return edges gives the value (2, 5). *)
  Example matched_return_value :
    A.finish tt (PathReturn None 0 2 None (Some tt) None None) [(1, 0); (2, 0)] = (2, 5).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The composition of the three affine functions applied to 4 gives 15. *)
  Example composed_affine_application :
    Affine.apply (Affine.compose (1, 1) (Affine.compose (2, 0) (1, 3))) 4 = 15.
  Proof.
    vm_compute; reflexivity.
  Qed.

End CompositionTests.

(** * Translation *)

Module TranslationTests.

  (** The affine rules equal the reference path rules. *)
  Example affine_rules_match_reference :
    affine_rules = path_rules NatKeyCode.eqb (Icfg.kind tt) (Graph.dst tt)
      (AffineFlow.facts tt) (AffineFlow.flow tt) (AffineFlow.seeds tt) (Graph.edges tt).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The affine checker accepts the lookup that gives the jump its values. *)
  Example affine_jump_accepted : affine_check affine_lookup = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The checker rejects the lookup that drops the value of the missing return. *)
  Example missing_return_rejected :
    affine_check (fun k => if Nat.eqb (fst (snd k)) 3 then FBot else affine_lookup k) = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Applying the translation of 1 to a large integer adds 1 to it. *)
  Example large_integer_translation :
    Translation.apply (FVal 1%Z) 1000000%Z = 1000001%Z.
  Proof.
    vm_compute; reflexivity.
  Qed.

End TranslationTests.

(** * Roots *)

Module RootTests.

  (** The affine function of a path row, if the row is an identity. *)
  Definition affine_root (r : ASys.row) := match path_row_rule r with
    | PathIdentity n d => Some (n, d)
    | _ => None
    end.

  (** The rule tags of a row: seed, root, step and return. *)
  Definition affine_rule_tags (r : ASys.row) : bool * bool * bool * bool :=
    match path_row_rule r with
    | PathIdentity n None => (Nat.eqb n 0, Nat.eqb n 1, false, false)
    | PathStep None e None None => (false, false, Nat.eqb e 1, false)
    | PathReturn None call ret None None None None =>
        (false, false, false, Nat.eqb call 0 && Nat.eqb ret 2)
    | _ => (false, false, false, false)
    end.

  (** The tags of all the rows, combined by or. *)
  Definition affine_seen := fold_left (fun acc r =>
    let '(seed, root, step, ret) := affine_rule_tags r in
    let '(a, b, c, d) := acc in (a || seed, b || root, c || step, d || ret))
    (ASys.rows tt) (false, false, false, false).

  (** The identity rows of the affine system are the roots 0 and 1 with no fact. *)
  Example affine_roots_listed :
    flat_map (fun r => match affine_root r with Some x => [x] | None => [] end) (ASys.rows tt) =
      [(0, None); (1, None)].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Some row of the affine system is a seed. *)
  Example seed_row_seen :
    let '(a, _, _, _) := affine_seen in a = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Some row of the affine system is a root. *)
  Example root_row_seen :
    let '(_, b, _, _) := affine_seen in b = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Some row of the affine system is a step over edge 1. *)
  Example step_row_seen :
    let '(_, _, c, _) := affine_seen in c = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Some row of the affine system is a return matched to call 0 and return 2. *)
  Example return_row_seen :
    let '(_, _, _, d) := affine_seen in d = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

End RootTests.

(** * Unchecked *)

Module UncheckedTests.

  (** A graph with the single entry 0 and no edges. *)
  Module Singleton <: CFG_OPS Prog NatKeyCode Edge.
    Definition entries (_ : unit) := [0].
    Definition edges (_ : unit) : list nat := [].
    Definition src (_ : unit) (e : nat) := e.
    Definition dst (_ : unit) (e : nat) := e.
  End Singleton.

  Module SingleIcfg <: ICFG_OPS Prog NatKeyCode Edge Singleton NatKeyCode.
    Definition kind (_ : unit) (_ : nat) : edge_kind nat := Intra.
  End SingleIcfg.

  (** A micro lattice of booleans that accepts every pair, with identity true and and as composition. *)
  Module BadMicro <: MICRO_OPS IfdsLatticeCode.
    Definition t := bool.
    Definition leb (_ _ : bool) := true.
    Definition bot := false.
    Definition is_bot := negb.
    Definition join (_ _ : bool) := true.
    Definition identity := true.
    Definition compose := andb.
    Definition apply := andb.
  End BadMicro.

  (** A flow with no facts after its seed, so every edge gives an empty flow. *)
  Module NoFlow <: IDE_FLOW_OPS Prog NatKeyCode Edge Fact IfdsLatticeCode BadMicro.
    Definition facts (_ : unit) : list (option unit) := [None].
    Definition flow (_ : unit) (_ : nat) (_ : option unit) : list (option unit) := [].
    Definition seeds (_ : unit) : list (nat * option unit) := [(0, None)].
    Definition weight (_ : unit) (_ : nat) (_ _ : option unit) := true.
  End NoFlow.

  Module NoFlowRules <: IFDS_RULES_OPS Prog NatKeyCode Edge Fact.
    Definition rules (_ : unit) : list (path_rule nat nat (option unit)) := [PathIdentity 0 None].
  End NoFlowRules.

  Module Bad := IdeCode Prog NatKeyCode Edge Singleton NatKeyCode SingleIcfg Fact
    IfdsLatticeCode BadMicro NoFlow NoFlowRules.

  (** Whether the lookup satisfies every row of the bad system. *)
  Definition bad_check lookup := forallb (fun r =>
    row_ok BadMicro.leb lookup (Bad.target tt r)
      (eval_query (Bad.resume tt) lookup (S (length (Bad.deps tt r))) (Bad.start tt r)))
    (Bad.rows tt).

  (** The empty lookup passes the bad checker, because its enumerated jump is not checked. *)
  Example empty_lookup_passes_bad_checker : bad_check (fun _ => false) = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The bad composition applies the identity to true as true. *)
  Example bad_identity_applies_true : BadMicro.apply BadMicro.identity true = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The bad composition applies false to true as false. *)
  Example bad_apply_of_false_is_false : BadMicro.apply false true = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  Module NoFlowIfds := IfdsCode Prog NatKeyCode Edge Singleton NatKeyCode SingleIcfg Fact
    NoFlow NoFlowRules IfdsLatticeCode.

  (** The lookup that holds only at the seed of the no-flow system. *)
  Definition no_flow_lookup k := NoFlowIfds.key_eqb k (None, (0, None)).

  (** The no-flow system is accepted by the lookup that holds at its seed. *)
  Example no_flow_identity_passes : forallb (fun r =>
    row_ok IfdsLatticeCode.leb no_flow_lookup (NoFlowIfds.target tt r)
      (eval_query (NoFlowIfds.resume tt) no_flow_lookup
        (S (length (NoFlowIfds.deps tt r))) (NoFlowIfds.start tt r)))
    (NoFlowIfds.rows tt) = true.
  Proof.
    vm_compute; reflexivity.
  Qed.

End UncheckedTests.
