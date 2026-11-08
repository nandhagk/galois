(** * Tarjan's component visitor

    The visitor maintains discovery numbers, low links and a pending component stack.
    For example, closing the root of a cycle pops all its members into one component.
    Builds on: GraphSearch, GraphSccSpec and the costed maps and sets. *)

From Stdlib Require Import List Bool PArith NArith.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseMap BaseSet.
From Galois.Graph Require Import GraphPrepared GraphVisitor GraphSearchSpec GraphSearch GraphSccSpec.
Import List.ListNotations Cost.Notations.

Module Tarjan.

(** Component lists accumulate backwards while ownership uses increasing one-based indices. *)
Record state := State {
  disc : Map.t positive positive;
  low : Map.t positive positive;
  stack : list positive;
  on_stack : FinSet.t positive;
  emitted_rev : list (list positive);
  owners : Map.t positive positive;
  clock : positive;
  next_component : positive
}.

(** Initial storage is empty and both next one-based counters start at one. *)
Definition initial :=
  State Map.empty Map.empty [] FinSet.empty [] Map.empty 1%positive 1%positive.

(** A pop returns its consumed prefix, untouched suffix and updated pending and owner indexes. *)
Record popped := Popped {
  members : list positive;
  tail : list positive;
  links : Map.t positive positive;
  pending : FinSet.t positive;
  component_owners : Map.t positive positive
}.

(** Popping charges each consumed cell, key comparison and low-link, set and owner update. *)
Fixpoint pop_c root i xs lows active own : Cost.t popped :=
  match xs with
  | [] => Cost.ret (Popped [] [] lows active own)
  | v :: rest =>
    Cost.step ;;
    let* lows' := Map.remove_c positive_encoding v lows in
    let* active' := FinSet.remove_c positive_encoding v active in
    let* own' := Map.set_c positive_encoding v i own in
    let* equal := Map.code_compare_c v root in
    match equal with
    | Eq => Cost.ret (Popped [v] rest lows' active' own')
    | _ =>
      let* answer := pop_c root i rest lows' active' own' in
      Cost.ret (Popped (v :: members answer) (tail answer) (links answer)
        (pending answer) (component_owners answer))
    end
  end.

Definition pop root i xs lows active own := Cost.value (pop_c root i xs lows active own).

(** The pop equation exposes the exact prefix cut without a second stack traversal. *)
Theorem pop_equation root i xs lows active own :
  pop root i xs lows active own =
  match xs with
  | [] => Popped [] [] lows active own
  | v :: rest =>
    let lows' := Map.remove positive_encoding v lows in
    let active' := FinSet.remove positive_encoding v active in
    let own' := Map.set positive_encoding v i own in
    match Map.code_compare v root with
    | Eq => Popped [v] rest lows' active' own'
    | _ =>
      let answer := pop root i rest lows' active' own' in
      Popped (v :: members answer) (tail answer) (links answer)
        (pending answer) (component_owners answer)
    end
  end.
Proof.
  destruct xs as [|v rest]; [reflexivity|].
  unfold pop at 1. cbn [pop_c]. autorewrite with galois_cost.
  fold (Map.code_compare v root).
  destruct (Map.code_compare v root); reflexivity.
Qed.

(** Entry charges the discovery, low-link and pending-set insertions before pushing the vertex. *)
Definition enter_c v (s : state) :=
  Cost.step ;;
  let* numbers := Map.set_c positive_encoding v (clock s) (disc s) in
  let* lows := Map.set_c positive_encoding v (clock s) (low s) in
  let* active := FinSet.add_c positive_encoding v (on_stack s) in
  Cost.ret (State numbers lows (v :: stack s) active (emitted_rev s) (owners s)
    (Pos.succ (clock s)) (next_component s)).

Definition enter v s := Cost.value (enter_c v s).

(** Entry allocates one discovery number and pushes one pending vertex. *)
Theorem enter_equation v s :
  enter v s =
    State (Map.set positive_encoding v (clock s) (disc s))
      (Map.set positive_encoding v (clock s) (low s)) (v :: stack s)
      (FinSet.add positive_encoding v (on_stack s)) (emitted_rev s) (owners s)
      (Pos.succ (clock s)) (next_component s).
Proof.
  reflexivity.
Qed.

(** Lowering charges an existing low-link minimum update and leaves a missing link absent. *)
Definition lower_c v n (s : state) :=
  Cost.step ;;
  let* old := Map.get_c positive_encoding v (low s) in
  match old with
  | None => Cost.ret s
  | Some old =>
    let* lows := Map.set_c positive_encoding v (Pos.min old n) (low s) in
    Cost.ret (State (disc s) lows (stack s) (on_stack s) (emitted_rev s) (owners s)
      (clock s) (next_component s))
  end.

Definition lower v n s := Cost.value (lower_c v n s).

(** Lowering keeps missing links absent and takes the minimum at an existing link. *)
Theorem lower_equation v n s :
  lower v n s =
    match Map.get positive_encoding v (low s) with
    | None => s
    | Some old =>
      State (disc s) (Map.set positive_encoding v (Pos.min old n) (low s))
        (stack s) (on_stack s) (emitted_rev s) (owners s) (clock s) (next_component s)
    end.
Proof.
  unfold lower, lower_c. autorewrite with galois_cost.
  fold (Map.get positive_encoding v (low s)).
  destruct (Map.get positive_encoding v (low s)); reflexivity.
Qed.

(** A non-tree edge lowers its source only when its target is still pending. *)
Definition edge_c u v k (s : state) :=
  Cost.step ;;
  match k with
  | Search.Tree => Cost.ret s
  | _ =>
    let* active := FinSet.mem_c positive_encoding v (on_stack s) in
    if active then
      let* number := Map.get_c positive_encoding v (disc s) in
      match number with
      | None => Cost.ret s
      | Some number => lower_c u number s
      end
    else Cost.ret s
  end.

Definition edge u v k s := Cost.value (edge_c u v k s).

(** Edge updates use target discovery numbers, including cross edges into pending components. *)
Theorem edge_equation u v k s :
  edge u v k s =
    match k with
    | Search.Tree => s
    | _ =>
      if FinSet.mem positive_encoding v (on_stack s) then
        match Map.get positive_encoding v (disc s) with
        | None => s
        | Some number => lower u number s
        end
      else s
    end.
Proof.
  destruct k; unfold edge, edge_c; autorewrite with galois_cost; [reflexivity| | |].
  all: fold (FinSet.mem positive_encoding v (on_stack s)).
  all: destruct (FinSet.mem positive_encoding v (on_stack s)); [|reflexivity].
  all: autorewrite with galois_cost; fold (Map.get positive_encoding v (disc s)).
  all: destruct (Map.get positive_encoding v (disc s)); reflexivity.
Qed.

(** Emission charges a real prefix pop and advances the chronological component counter. *)
Definition emit_c root (s : state) :=
  Cost.step ;;
  let* answer := pop_c root (next_component s) (stack s) (low s) (on_stack s) (owners s) in
  Cost.ret (State (disc s) (links answer) (tail answer) (pending answer)
    (members answer :: emitted_rev s) (component_owners answer) (clock s)
    (Pos.succ (next_component s))).

Definition emit root s := Cost.value (emit_c root s).

(** Emission transfers the popped prefix from pending membership to one new component owner. *)
Theorem emit_equation root s :
  emit root s =
    let answer := pop root (next_component s) (stack s) (low s) (on_stack s) (owners s) in
    State (disc s) (links answer) (tail answer) (pending answer)
      (members answer :: emitted_rev s) (component_owners answer) (clock s)
      (Pos.succ (next_component s)).
Proof.
  reflexivity.
Qed.

(** Exit either emits a component root or propagates a pending child's low link to its parent. *)
Definition exit_c v parent (s : state) :=
  Cost.step ;;
  let* l := Map.get_c positive_encoding v (low s) in
  let* d := Map.get_c positive_encoding v (disc s) in
  match l, d with
  | Some l, Some d =>
    if Pos.eqb l d then emit_c v s else
    match parent with
    | None => Cost.ret s
    | Some u => lower_c u l s
    end
  | _, _ => Cost.ret s
  end.

Definition exit v parent s := Cost.value (exit_c v parent s).

(** The exit equation makes missing discovery data explicit without inventing a rank. *)
Theorem exit_equation v parent s :
  exit v parent s =
    match Map.get positive_encoding v (low s), Map.get positive_encoding v (disc s) with
    | Some l, Some d =>
      if Pos.eqb l d then emit v s else
      match parent with
      | None => s
      | Some u => lower u l s
      end
    | _, _ => s
    end.
Proof.
  unfold exit, exit_c. autorewrite with galois_cost.
  fold (Map.get positive_encoding v (low s)).
  fold (Map.get positive_encoding v (disc s)).
  destruct (Map.get positive_encoding v (low s)) as [l|];
    destruct (Map.get positive_encoding v (disc s)) as [d|]; try reflexivity.
  destruct (Pos.eqb l d); [reflexivity|]. destruct parent; reflexivity.
Qed.

(** The visitor dispatches Tarjan updates without inspecting or controlling Search frames. *)
Definition visitor {E} : Visitor.t E state :=
  Visitor.Make (fun v _ => enter_c v) (fun _ => edge_c) exit_c.

(** Result construction pays for reversing the emitted component accumulator. *)
Definition result_c (s : state) :=
  let* components := rev_c (emitted_rev s) in Cost.ret (Scc.Result components (owners s)).

Definition result s := Cost.value (result_c s).

(** Finalisation reverses the component accumulator and retains the existing one-based owners. *)
Theorem result_equation s : result s = Scc.Result (rev (emitted_rev s)) (owners s).
Proof.
  unfold result, result_c. autorewrite with galois_cost. reflexivity.
Qed.

(** Computing components invokes the shared search exactly once and performs no preparation scan. *)
Definition compute_c {V E} (p : Prepared.t V E) scope roots :=
  let* answer := SearchRun.run_c p visitor scope roots initial in result_c (snd answer).

(** The plain producer is exactly the value of its single costed computation. *)
Definition compute {V E} (p : Prepared.t V E) scope roots :=
  Cost.value (compute_c p scope roots).

(** Component computation is finalisation of the actual visitor state returned by search. *)
Theorem compute_equation {V E} (p : Prepared.t V E) scope roots :
  compute p scope roots = result (snd (Cost.value (SearchRun.run_c p visitor scope roots initial))).
Proof.
  reflexivity.
Qed.

End Tarjan.
