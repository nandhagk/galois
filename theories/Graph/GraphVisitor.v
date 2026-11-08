(** * Search events and stateful visitors

    Visitors consume events independently of the search stack.
    For example, pairing two counters updates both and adds their callback charges.
    Builds on: CostMonad and BaseSet. *)

From Stdlib Require Import List Bool NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseSet.
Import List.ListNotations Cost.Notations.

Module Scope.

Record t := Make {
  blocked : FinSet.t positive;
  within : option (FinSet.t positive)
}.

Definition admits_c s v :=
  Cost.step ;;
  let* blocked := FinSet.mem_c positive_encoding v (blocked s) in
  if blocked then Cost.ret false else
  match within s with
  | None => Cost.ret true
  | Some region => FinSet.mem_c positive_encoding v region
  end.

Definition admits s v := Cost.value (admits_c s v).

(** Admission excludes blocked IDs and requires optional-region membership. *)
Theorem admits_equation s v :
  admits s v =
    (negb (FinSet.mem positive_encoding v (blocked s)) &&
      match within s with
      | None => true
      | Some region => FinSet.mem positive_encoding v region
      end)%bool.
Proof.
  unfold admits, admits_c. autorewrite with galois_cost.
  fold (FinSet.mem positive_encoding v (blocked s)).
  destruct (FinSet.mem positive_encoding v (blocked s)); [reflexivity|].
  destruct (within s); reflexivity.
Qed.

(** Admission charges the blocked query and any selected region query. *)
Theorem admits_cost_equation s v :
  Cost.ticks (admits_c s v) =
    (1 + Cost.ticks (FinSet.mem_c positive_encoding v (blocked s)) +
      if FinSet.mem positive_encoding v (blocked s) then 0 else
      match within s with
      | None => 0
      | Some region => Cost.ticks (FinSet.mem_c positive_encoding v region)
      end)%N.
Proof.
  unfold admits_c. autorewrite with galois_cost.
  fold (FinSet.mem positive_encoding v (blocked s)).
  destruct (FinSet.mem positive_encoding v (blocked s)).
  - autorewrite with galois_cost. lia.
  - destruct (within s); autorewrite with galois_cost; lia.
Qed.

Arguments admits_c s v : simpl never.
Arguments admits s v : simpl never.

End Scope.

Module Search.

Inductive kind :=
  | Tree
  | Back
  | Forward
  | Cross.

Inductive event (E : Type) :=
  | Enter (v : positive) (via : option (E * positive))
  | Edge (e : E) (u v : positive) (k : kind)
  | Exit (v : positive) (parent : option positive).
Arguments Enter {E}.
Arguments Edge {E}.
Arguments Exit {E}.

End Search.

Module Visitor.

Record t (E S : Type) := Make {
  on_enter_c : positive -> option (E * positive) -> S -> Cost.t S;
  on_edge_c : E -> positive -> positive -> Search.kind -> S -> Cost.t S;
  on_exit_c : positive -> option positive -> S -> Cost.t S
}.
Arguments Make {E S}.
Arguments on_enter_c {E S}.
Arguments on_edge_c {E S}.
Arguments on_exit_c {E S}.

Definition on_enter {E S} (v : t E S) n via s := Cost.value (on_enter_c v n via s).
Definition on_edge {E S} (v : t E S) e a b k s := Cost.value (on_edge_c v e a b k s).
Definition on_exit {E S} (v : t E S) n par s := Cost.value (on_exit_c v n par s).

(** Each pure visitor primitive charges one tick independently of event dispatch. *)
Definition of_pure {E S}
    (enter : positive -> option (E * positive) -> S -> S)
    (edge : E -> positive -> positive -> Search.kind -> S -> S)
    (exit : positive -> option positive -> S -> S) : t E S :=
  Make (fun v via => Cost.lift (fun _ => 1%N) (enter v via))
    (fun e u v k => Cost.lift (fun _ => 1%N) (edge e u v k))
    (fun v par => Cost.lift (fun _ => 1%N) (exit v par)).

Definition noop {E S} : t E S :=
  Make (fun _ _ s => Cost.ret s) (fun _ _ _ _ s => Cost.ret s)
    (fun _ _ s => Cost.ret s).

Definition apply_c {E S} (vis : t E S) (event : Search.event E) s :=
  Cost.step ;;
  match event with
  | Search.Enter v via => on_enter_c vis v via s
  | Search.Edge e u v k => on_edge_c vis e u v k s
  | Search.Exit v par => on_exit_c vis v par s
  end.

Definition apply {E S} (vis : t E S) ev s := Cost.value (apply_c vis ev s).

Definition both_c {A B} (a : Cost.t A) (b : Cost.t B) :=
  Cost.step ;;
  let* x := a in
  Cost.step ;;
  let* y := b in Cost.ret (x, y).

Definition pair {E A B} (a : t E A) (b : t E B) : t E (A * B) :=
  Make
    (fun v via s => both_c (on_enter_c a v via (fst s)) (on_enter_c b v via (snd s)))
    (fun e u v k s => both_c (on_edge_c a e u v k (fst s))
      (on_edge_c b e u v k (snd s)))
    (fun v par s => both_c (on_exit_c a v par (fst s)) (on_exit_c b v par (snd s))).

(** Potential is added before comparison, avoiding truncated-subtraction contracts. *)
Definition amortised {E S} (vis : t E S) (Phi : S -> N) (k : N) : Prop :=
  forall ev s,
    (Cost.ticks (apply_c vis ev s) + Phi (apply vis ev s) <= k + Phi s)%N.

(** Local amortisation preserves a visitor-state invariant on a specified event domain. *)
Definition amortised_on {E S} (vis : t E S) (I : S -> Prop)
    (D : Search.event E -> Prop) (Phi : S -> N) (k : N) : Prop :=
  forall ev s, I s -> D ev ->
    I (apply vis ev s) /\
    (Cost.ticks (apply_c vis ev s) + Phi (apply vis ev s) <= k + Phi s)%N.

(** A global cost law restricts to any event domain whose callbacks preserve the invariant. *)
Theorem amortised_on_of_global {E S} (vis : t E S) I D Phi k :
  amortised vis Phi k ->
  (forall ev s, I s -> D ev -> I (apply vis ev s)) ->
    amortised_on vis I D Phi k.
Proof.
  intros Hcost Hpreserve ev s HI HD. split.
  - exact (Hpreserve ev s HI HD).
  - apply Hcost.
Qed.

(** A local callback law remains valid when its event domain is restricted. *)
Theorem amortised_on_restrict {E S} (vis : t E S) I D D' Phi k :
  amortised_on vis I D Phi k -> (forall ev, D' ev -> D ev) ->
    amortised_on vis I D' Phi k.
Proof.
  intros Hlocal Hdomain ev s HI HD. apply Hlocal; [exact HI|now apply Hdomain].
Qed.

(** Pairing runs both visitors on their respective state components. *)
Theorem pair_apply {E A B} (a : t E A) (b : t E B) ev x y :
  apply (pair a b) ev (x, y) = (apply a ev x, apply b ev y).
Proof.
  destruct ev; reflexivity.
Qed.

(** Pairing retains both visitor charges and adds one net dispatch tick. *)
Theorem pair_apply_cost {E A B} (a : t E A) (b : t E B) ev x y :
  Cost.ticks (apply_c (pair a b) ev (x, y)) =
    (1 + Cost.ticks (apply_c a ev x) + Cost.ticks (apply_c b ev y))%N.
Proof.
  destruct ev; unfold apply_c, pair, both_c;
    cbn [on_enter_c on_edge_c on_exit_c fst snd];
    autorewrite with galois_cost; lia.
Qed.

(** A no-op visitor preserves state and charges only the event dispatch. *)
Theorem noop_apply {E S} (ev : Search.event E) (s : S) :
  apply noop ev s = s /\ Cost.ticks (apply_c noop ev s) = 1%N.
Proof.
  destruct ev; split; reflexivity.
Qed.

(** A no-op visitor satisfies the unit amortised contract for every potential. *)
Theorem noop_amortised {E S} (Phi : S -> N) :
  amortised (@noop E S) Phi 1.
Proof.
  intros ev s. destruct (noop_apply ev s) as [Hvalue Hticks].
  rewrite Hticks, Hvalue. lia.
Qed.

(** Product potentials compose with the extra net dispatch charge. *)
Theorem pair_amortised {E A B} (a : t E A) (b : t E B) Phi Psi ka kb :
  amortised a Phi ka -> amortised b Psi kb ->
  amortised (pair a b) (fun s => (Phi (fst s) + Psi (snd s))%N) (1 + ka + kb).
Proof.
  intros Ha Hb ev [x y]. specialize (Ha ev x). specialize (Hb ev y).
  rewrite pair_apply_cost, pair_apply. cbn [fst snd]. lia.
Qed.

(** The no-op visitor preserves every local invariant and retains its full potential. *)
Theorem noop_amortised_on {E S} (I : S -> Prop) D (Phi : S -> N) :
  amortised_on (@noop E S) I D Phi 1.
Proof.
  apply amortised_on_of_global; [apply noop_amortised|].
  intros ev s HI HD. now rewrite (proj1 (noop_apply ev s)).
Qed.

(** Product visitors preserve both local invariants on the same event domain. *)
Theorem pair_amortised_on {E A B} (a : t E A) (b : t E B) I J D Phi Psi ka kb :
  amortised_on a I D Phi ka -> amortised_on b J D Psi kb ->
    amortised_on (pair a b) (fun s => I (fst s) /\ J (snd s)) D
      (fun s => (Phi (fst s) + Psi (snd s))%N) (1 + ka + kb).
Proof.
  intros Ha Hb ev [x y] [HI HJ] HD.
  destruct (Ha ev x HI HD) as [HI' Hcost].
  destruct (Hb ev y HJ HD) as [HJ' Hcost'].
  rewrite pair_apply, pair_apply_cost. cbn [fst snd]. split; [auto|lia].
Qed.

Arguments apply_c {E S} vis event s : simpl never.
Arguments pair {E A B} a b : simpl never.
Arguments noop {E S} : simpl never.

End Visitor.
