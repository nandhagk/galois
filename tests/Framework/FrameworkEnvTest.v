(** * Counter-loop state actions

    Interval states illustrate ordered assignment and guard actions without a Bits vocabulary.
    For example, the true counter edge restricts its input to values below three.
    Builds on: FrameworkEnv and FrameworkDenseTest. *)

From Stdlib Require Import List Bool ZArith NArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding.
From Galois.Lattice Require Import LatticeCore.
From Galois.Domains Require Import DomainsTerm DomainsState.
From Galois.Fixpoint Require Import FixpointSystem FixpointCheck FixpointAnalysis.
From Galois.Framework Require Import FrameworkEnv.
From Galois.Tests.Framework Require Import FrameworkDenseTest.
Import List.ListNotations Cost.Notations.
Local Open Scope Z_scope.

Inductive counter_op :=
  | Constant (z : Z)
  | Increment.

Inductive counter_guard :=
  | Below (z : Z)
  | AtLeast (z : Z).

Definition interval := option (Z * Z).

Definition interval_le (x y : interval) :=
  match x, y with
  | None, _ => true
  | Some (l, u), Some (l', u') => (l' <=? l) && (u <=? u')
  | Some _, None => false
  end.

Definition hull (x y : interval) :=
  match x, y with
  | None, _ => y
  | _, None => x
  | Some (l, u), Some (l', u') => Some (Z.min l l', Z.max u u')
  end.

Definition interval_lat := simple interval_le None hull.

Definition clip l u : interval := if l <=? u then Some (l, u) else None.

Definition counter_state : StateAbs.t interval interval unit counter_op counter_guard :=
  {| StateAbs.lat := interval_lat;
     StateAbs.top := Some (0, 3);
     StateAbs.assign_c := fun _ e st => Cost.step ;; Cost.ret
       (match st, e with
        | None, _ => None
        | Some _, Node (Constant z) [] => Some (z, z)
        | Some (l, u), Node Increment [Leaf _] => Some (l + 1, u + 1)
        | _, _ => st
        end);
     StateAbs.havoc_c := fun _ st => Cost.ret
       (match st with None => None | Some _ => Some (0, 3) end);
     StateAbs.assume_c := fun g _ st => Cost.step ;; Cost.ret
       (match st, g with
        | None, _ => None
        | Some (l, u), Below z => clip l (Z.min u (z - 1))
        | Some (l, u), AtLeast z => clip (Z.max l z) u
        end);
     StateAbs.project_c := fun _ st => Cost.ret st |}.

Definition counter_actions : Env.t nat nat unit counter_op counter_guard :=
  Env.Make loop unit_encoding (fun e => Cost.ret
    (match e with
    | O => [Env.Assign tt (Node (Constant 0) [])]
    | S O => [Env.Assume (Below 3) [Leaf tt]; Env.Assign tt (Node Increment [Leaf tt])]
    | _ => [Env.Assume (AtLeast 3) [Leaf tt]]
    end)).

Definition counter_policy : Policy.t nat :=
  Policy.Make (fun _ => Cost.ret 1%positive)
    (fun n => Cost.ret (Nat.eqb n 1)) 0 1.

Definition counter_analysis :=
  Env.analysis counter_actions counter_state (Some (0, 0)) counter_policy.

Example counter_loop_intervals :
  observe counter_analysis 16 [0%nat; 1%nat; 2%nat] =
    Some [Some (0, 0); Some (0, 3); Some (3, 3)].
Proof.
  vm_compute; reflexivity.
Qed.

Example counter_hand_candidate :
  check_post interval_lat (Analysis.system counter_analysis)
    (fun n => match n with
      | O => Some (0, 0)
      | S O => Some (0, 3)
      | _ => Some (3, 3)
      end) = true.
Proof.
  vm_compute; reflexivity.
Qed.

Example counter_bad_candidate :
  check_post interval_lat (Analysis.system counter_analysis) (fun _ => Some (0, 0)) = false.
Proof.
  vm_compute; reflexivity.
Qed.

Example ordered_assignment_guard :
  Env.apply_actions counter_state
    [Env.Assign tt (Node (Constant 2) []); Env.Assume (AtLeast 2) [Leaf tt]]
    (Some (0, 0)) = Some (2, 2).
Proof.
  vm_compute; reflexivity.
Qed.

Example reversed_actions_reject :
  Env.apply_actions counter_state
    [Env.Assume (AtLeast 2) [Leaf tt]; Env.Assign tt (Node (Constant 2) [])]
    (Some (0, 0)) = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example empty_actions :
  Env.apply_actions counter_state [] (Some (1, 2)) = Some (1, 2).
Proof.
  vm_compute; reflexivity.
Qed.

Example unreachable_havoc :
  Env.apply_actions counter_state [Env.Havoc tt] None = None.
Proof.
  vm_compute; reflexivity.
Qed.

Example requested_narrowing_round : Policy.narrowing (Analysis.policy counter_analysis) = 1%nat.
Proof.
  vm_compute; reflexivity.
Qed.

Definition charged_state : StateAbs.t bool bool unit unit unit :=
  {| StateAbs.lat := simple implb false orb;
     StateAbs.top := true;
     StateAbs.assign_c := fun _ _ s => Cost.ret s;
     StateAbs.havoc_c := fun _ s => Cost.tick 17 ;; Cost.ret s;
     StateAbs.assume_c := fun _ _ s => Cost.ret s;
     StateAbs.project_c := fun _ s => Cost.ret s |}.

Example action_retains_callback_and_invocation :
  Cost.ticks (Env.apply_actions_c charged_state [Env.Havoc tt] true) = 19%N.
Proof.
  vm_compute; reflexivity.
Qed.
