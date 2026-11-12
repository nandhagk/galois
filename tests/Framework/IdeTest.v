(** * IDE composition observations

    Matched returns compose caller, call, callee and return functions.
    For example, reversing the call and return changes the observed affine result.
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

Module Values <: LATTICE_OPS.
  Definition t := nat.
  Definition leb := Nat.leb.
  Definition bot := 0.
  Definition is_bot n := Nat.eqb n 0.
  Definition join := Nat.max.
End Values.
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
Module Flow <: IDE_FLOW_OPS Prog NatKeyCode Edge Fact Values Affine.
  Definition facts := Flow.facts.
  Definition flow := Flow.flow.
  Definition seeds := Flow.seeds.
  Definition weight (_ : unit) e (_ _ : option unit) : Affine.t :=
    match e with 0 => (1, 1) | 2 => (1, 3) | _ => (1, 0) end.
End Flow.
Module A := IdeCode Prog NatKeyCode Edge Graph NatKeyCode Icfg Fact Values Affine Flow Rules.

Example matched_return_composition_is_not_reversed :
  (A.finish tt (PathReturn None 0 2 None (Some tt) None None) [(1, 0); (2, 0)],
   Affine.apply (Affine.compose (1, 1) (Affine.compose (2, 0) (1, 3))) 4) =
    ((2, 5), 15).
Proof. vm_compute; reflexivity. Qed.

Module ZValues <: LATTICE_OPS.
  Definition t := Z.
  Definition leb := Z.leb.
  Definition bot := 0%Z.
  Definition is_bot n := Z.eqb n 0%Z.
  Definition join := Z.max.
End ZValues.

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
Module AffineFlow <: IDE_FLOW_OPS Prog NatKeyCode Edge Fact ZValues Translation.
  Definition facts (_ : unit) : list (option unit) := [None].
  Definition flow (_ : unit) (_ : nat) (d : option unit) := [d].
  Definition seeds (_ : unit) : list (nat * option unit) := [(0, None)].
  Definition weight (_ : unit) e (_ _ : option unit) : Translation.t :=
    FVal (if Nat.eqb e 1 then 1%Z else 0%Z).
End AffineFlow.
Definition affine_rules := Eval vm_compute in
  path_rules NatKeyCode.eqb (Icfg.kind tt) (Graph.dst tt) (AffineFlow.facts tt)
    (AffineFlow.flow tt) (AffineFlow.seeds tt) (Graph.edges tt).
Module AffineRules <: IFDS_RULES_OPS Prog NatKeyCode Edge Fact.
  Definition rules (_ : unit) := affine_rules.
End AffineRules.
Module ASys := IdeCode Prog NatKeyCode Edge Graph NatKeyCode Icfg Fact ZValues Translation
  AffineFlow AffineRules.
Definition affine_lookup (k : ASys.key) : Translation.t :=
  match snd k with
  | (0, None) | (1, None) => FVal 0%Z
  | (2, None) | (3, None) => FVal 1%Z
  | _ => FBot
  end.
Definition affine_check lookup := forallb (fun r =>
  row_ok Translation.leb lookup (ASys.target tt r)
    (eval_query (ASys.resume tt) lookup (S (length (ASys.deps tt r))) (ASys.start tt r)))
  (ASys.rows tt).

Example affine_jump_accepts : affine_check affine_lookup = true.
Proof. vm_compute; reflexivity. Qed.

Example affine_jump_rejects_missing_return :
  affine_check (fun k => if Nat.eqb (fst (snd k)) 3 then FBot else affine_lookup k) = false.
Proof. vm_compute; reflexivity. Qed.

Example affine_different_unlisted_integer : Translation.apply (FVal 1%Z) 1000000%Z = 1000001%Z.
Proof. vm_compute; reflexivity. Qed.

Module Singleton <: CFG_OPS Prog NatKeyCode Edge.
  Definition entries (_ : unit) := [0].
  Definition edges (_ : unit) : list nat := [].
  Definition src (_ : unit) (e : nat) := e.
  Definition dst (_ : unit) (e : nat) := e.
End Singleton.
Module SingleIcfg <: ICFG_OPS Prog NatKeyCode Edge Singleton NatKeyCode.
  Definition kind (_ : unit) (_ : nat) : edge_kind nat := Intra.
End SingleIcfg.
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
Definition bad_check lookup := forallb (fun r =>
  row_ok BadMicro.leb lookup (Bad.target tt r)
    (eval_query (Bad.resume tt) lookup (S (length (Bad.deps tt r))) (Bad.start tt r)))
  (Bad.rows tt).

Example bad_order_empty_jump_passes_enumerated_checker : bad_check (fun _ => false) = true.
Proof. vm_compute; reflexivity. Qed.

Example bad_order_accepted_bound_loses_identity_application :
  (BadMicro.apply BadMicro.identity true, BadMicro.apply false true) = (true, false).
Proof. vm_compute; reflexivity. Qed.

Module NoFlowIfds := IfdsCode Prog NatKeyCode Edge Singleton NatKeyCode SingleIcfg Fact
  NoFlow NoFlowRules IfdsLatticeCode.

Definition no_flow_lookup k := NoFlowIfds.key_eqb k (None, (0, None)).

Example no_flow_identity : forallb (fun r =>
  row_ok IfdsLatticeCode.leb no_flow_lookup (NoFlowIfds.target tt r)
    (eval_query (NoFlowIfds.resume tt) no_flow_lookup
      (S (length (NoFlowIfds.deps tt r))) (NoFlowIfds.start tt r)))
  (NoFlowIfds.rows tt) = true.
Proof. vm_compute; reflexivity. Qed.

Definition affine_root (r : ASys.row) := match path_row_rule r with
  | PathIdentity n d => Some (n, d)
  | _ => None
  end.

Example affine_prepared_roots :
  flat_map (fun r => match affine_root r with Some x => [x] | None => [] end) (ASys.rows tt) = [(0, None); (1, None)].
Proof. vm_compute; reflexivity. Qed.

Definition affine_rule_tags (r : ASys.row) : bool * bool * bool * bool :=
  match path_row_rule r with
  | PathIdentity n None => (Nat.eqb n 0, Nat.eqb n 1, false, false)
  | PathStep None e None None => (false, false, Nat.eqb e 1, false)
  | PathReturn None call ret None None None None =>
      (false, false, false, Nat.eqb call 0 && Nat.eqb ret 2)
  | _ => (false, false, false, false)
  end.
Definition affine_seen := fold_left (fun acc r =>
  let '(seed, root, step, ret) := affine_rule_tags r in
  let '(a, b, c, d) := acc in (a || seed, b || root, c || step, d || ret))
  (ASys.rows tt) (false, false, false, false).

Example affine_seed_call_path_return_rows : affine_seen = (true, true, true, true).
Proof. vm_compute; reflexivity. Qed.
