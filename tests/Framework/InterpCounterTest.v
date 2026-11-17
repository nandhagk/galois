(** * Interval counter actions

    Interval actions run through interpreter rows and checked worklist outcomes.
    For example, assignment followed by a guard yields the singleton interval two.

    Groups:
    - Actions: the order of the actions decides whether the guard passes, and havoc keeps unreachable states.
    - Loop: the counter loop starts from the top interval, and the candidates for it are checked.

    Builds on: Framework.Interp and Fixpoint.Certified. *)

From Stdlib Require Import List Bool ZArith NArith.
From Galois.Base Require Import KeySig Key Trie Heap.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import StateSig.
From Galois.Fixpoint Require Import Query PolicySig SolverSig Policy Check Narrow Worklist
  Certified.
From Galois.Program Require Import CfgSig.
From Galois.Framework Require Import InterpSig Interp.
Import List.ListNotations.

(** * Fixtures *)

(** Operations of the counter language: a constant, and an increment of one operand. *)
Inductive counter_op :=
  | Constant (z : Z)
  | Increment.

(** Guards of the counter language: below a bound, and at least a bound. *)
Inductive counter_guard :=
  | Below (z : Z)
  | AtLeast (z : Z).

(** The counter language, whose values are integers. *)
Module Lang <: LANG_OPS.
  Definition op := counter_op.
  Definition guard := counter_guard.
  Definition val := Z.
  Definition eval k cs :=
    match k, cs with
    | Constant z, [] => Some z
    | Increment, [x] => Some (x + 1)%Z
    | _, _ => None
    end.
  Definition literal k := match k with Constant z => Some z | _ => None end.
End Lang.

(** An interval, where None is the empty interval. *)
Definition interval := option (Z * Z).

(** The interval from l to u, or None when l is above u. *)
Definition clip l u : interval := if (l <=? u)%Z then Some (l, u) else None.

(** Intervals ordered by inclusion, with the bounds 0 to 3 as top. *)
Module V <: VALUE_DOMAIN_OPS Lang.
  Definition t := interval.
  Definition leb (x y : t) :=
    match x, y with
    | None, _ => true
    | Some (l, u), Some (l', u') => (l' <=? l)%Z && (u <=? u')%Z
    | Some _, None => false
    end.
  Definition bot : t := None.
  Definition is_bot (x : t) := match x with None => true | _ => false end.
  Definition join (x y : t) :=
    match x, y with
    | None, _ => y
    | _, None => x
    | Some (l, u), Some (l', u') => Some (Z.min l l', Z.max u u')
    end.
  Definition meet (x y : t) :=
    match x, y with
    | Some (l, u), Some (l', u') => clip (Z.max l l') (Z.min u u')
    | _, _ => None
    end.
  Definition top : t := Some (0%Z, 3%Z).
  Definition wparam := unit.
  Definition widen (_ : unit) := join.
  Definition narrow (a _ : t) := a.
  Definition forward k (xs : list t) : t :=
    match k, xs with
    | Constant z, [] => Some (z, z)
    | Increment, [Some (l, u)] => Some ((l + 1)%Z, (u + 1)%Z)
    | _, _ => None
    end.
  Definition backward (_ : counter_op) (_ : t) (xs : list t) := xs.
  Definition guard (_ : counter_guard) (xs : list t) := xs.
End V.

(** The state domain over intervals, with assignment, havoc, assumption and evaluation. *)
Module D <: STATE_DOMAIN_OPS UnitKeyCode Lang V.
  Definition t := V.t.
  Definition leb := V.leb.
  Definition bot := V.bot.
  Definition is_bot := V.is_bot.
  Definition top := V.top.
  Definition join := V.join.
  Definition meet := V.meet.
  Definition wparam := V.wparam.
  Definition widen := V.widen.
  Definition narrow := V.narrow.
  Definition assign (_ : unit) (e : term counter_op unit) st : t :=
    match st, e with
    | None, _ => None
    | Some _, Node (Constant z) [] => Some (z, z)
    | Some (l, u), Node Increment [Leaf _] => Some ((l + 1)%Z, (u + 1)%Z)
    | _, _ => st
    end.
  Definition havoc (_ : unit) (st : t) : t := match st with None => None | Some _ => top end.
  Definition assume g (_ : list (term counter_op unit)) st : t :=
    match st, g with
    | None, _ => None
    | Some (l, u), Below z => clip l (Z.min u (z - 1))
    | Some (l, u), AtLeast z => clip (Z.max l z) u
    end.
  Definition eval e st : t :=
    match eval_term (fun k xs => Some (V.forward k xs)) (fun _ : unit => st) e with
    | Some out => out
    | None => None
    end.
End D.

Module Prog <: TYPE. Definition t := unit. End Prog.
Module Edge <: TYPE. Definition t := list (action counter_op counter_guard unit). End Edge.

(** A CFG with one entry, 0, and one edge from 0 to 1. *)
Module Cfg <: CFG_OPS Prog NatKeyCode Edge.
  Definition entries (_ : unit) := [0].
  Definition edges (_ : unit) : list Edge.t := [].
  Definition src (_ : unit) (_ : Edge.t) := 0.
  Definition dst (_ : unit) (_ : Edge.t) := 1.
End Cfg.

(** Each edge is its own list of actions. *)
Module Actions <: ACTIONS_OPS Prog Edge UnitKeyCode Lang.
  Definition actions (_ : unit) (e : Edge.t) := e.
End Actions.

Module S := InterpCode Prog NatKeyCode Edge Cfg UnitKeyCode Lang V Actions D.

(** Edges of the counter CFG are numbered by nat. *)
Module CounterEdge <: TYPE. Definition t := nat. End CounterEdge.

(** A CFG with the edges 0, 1 and 2, from 0 to 1, from 1 to 1, and from 1 to 2. *)
Module CounterCfg <: CFG_OPS Prog NatKeyCode CounterEdge.
  Definition entries (_ : unit) := [0].
  Definition edges (_ : unit) := [0; 1; 2].
  Definition src (_ : unit) e := if Nat.eqb e 0 then 0 else 1.
  Definition dst (_ : unit) e := if Nat.eqb e 2 then 2 else 1.
End CounterCfg.

(** The counter loop: edge 0 assigns 0, edge 1 increments below 3, and edge 2 needs at least 3. *)
Module CounterActions <: ACTIONS_OPS Prog CounterEdge UnitKeyCode Lang.
  Definition actions (_ : unit) e : Edge.t :=
    match e with
    | O => [Assign tt (Node (Constant 0) [])]
    | S O => [Assume (Below 3) [Leaf tt]; Assign tt (Node Increment [Leaf tt])]
    | _ => [Assume (AtLeast 3) [Leaf tt]]
    end.
End CounterActions.

Module CS := InterpCode Prog NatKeyCode CounterEdge CounterCfg UnitKeyCode Lang V CounterActions D.
Module C := CheckCode D CS.
Module R := NarrowCode D CS C.
Module P := PolicyCode D.
Module W := WorklistCode D CS P HeapCode.
Module A := CertifiedCode D CS W C R.

(** * Actions *)

Module ActionsTests.

  (** Runs the actions on the state, and gives the outcome, or None when they do not return. *)
  Definition apply_actions acts a :=
    match S.resume tt acts a with Ret out => out | _ => None end.

  (** Assigning 2 and then guarding for at least 2 gives the singleton interval 2. *)
  Example assignment_then_guard :
    apply_actions [Assign tt (Node (Constant 2) []); Assume (AtLeast 2) [Leaf tt]]
      (Some (0%Z, 0%Z)) = Some (2%Z, 2%Z).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Guarding for at least 2 before the assignment rejects the state. *)
  Example guard_then_assignment_rejects :
    apply_actions [Assume (AtLeast 2) [Leaf tt]; Assign tt (Node (Constant 2) [])]
      (Some (0%Z, 0%Z)) = None.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** No actions keep the interval as it is. *)
  Example empty_actions_keep_state :
    apply_actions [] (Some (1%Z, 2%Z)) = Some (1%Z, 2%Z).
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** Havoc on an unreachable state keeps it unreachable. *)
  Example havoc_keeps_unreachable :
    apply_actions [Havoc tt] None = None.
  Proof.
    vm_compute; reflexivity.
  Qed.

End ActionsTests.

(** * Loop *)

Module LoopTests.

  (** The policy that makes node 1 a head, with one narrowing pass. *)
  Definition pol : policy unit := Policy unit PTrieCode.empty
    (PTrieCode.set (NatKeyCode.encode 1) (HeadCfg 0%N 0) PTrieCode.empty) tt 1.

  (** The entry interval of the counter loop is the top interval 0 to 3. *)
  Example entry_interval_is_top :
    match A.analyze tt pol 16%N with
    | Solved m => Some (map (C.look m) [0; 1; 2])
    | _ => None
    end = Some [Some (0%Z, 3%Z); Some (0%Z, 3%Z); Some (3%Z, 3%Z)].
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The hand candidate for the counter loop is rejected, because its entry is not top. *)
  Definition hand := PTrieCode.set (NatKeyCode.encode 0) (0, Some (0%Z, 0%Z))
    (PTrieCode.set (NatKeyCode.encode 1) (1, Some (0%Z, 3%Z))
      (PTrieCode.set (NatKeyCode.encode 2) (2, Some (3%Z, 3%Z)) PTrieCode.empty)).

  Example hand_candidate_rejected : C.check tt hand = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** A candidate that gives the entry interval 0 to 0 at every node is rejected. *)
  Definition bad := fold_right (fun n m =>
    PTrieCode.set (NatKeyCode.encode n) (n, Some (0%Z, 0%Z)) m)
    PTrieCode.empty [0; 1; 2].

  Example bad_candidate_rejected : C.check tt bad = false.
  Proof.
    vm_compute; reflexivity.
  Qed.

  (** The policy passes once through the narrowing. *)
  Example single_narrowing_pass : passes pol = 1%nat.
  Proof.
    vm_compute; reflexivity.
  Qed.

End LoopTests.
