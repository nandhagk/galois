(** * Environment state fixtures

    Open integer points exercise assignments, refinements and the top-default boundary.
    For example, copying a variable retains its point and havoc replaces it with top.
    Builds on: DomainsEnv and DomainsPoint. *)

From Stdlib Require Import List Bool ZArith NArith.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap.
From Galois.Lattice Require Import LatticeCore LatticeConcrete LatticeEnv LatticeAdjoin.
From Galois.Domains Require Import DomainsValue DomainsTerm DomainsState DomainsPoint DomainsEnv.
Import List.ListNotations Cost.Notations.

Local Open Scope Z_scope.

Module EnvFixture.

Definition gam : concretisation point Z := {| gamma := point_gamma 1%positive |}.

Definition meet a b := Cost.step ;; Cost.ret (point_meet a b).

Definition values : ValueAbs.t point Z Z :=
  {| ValueAbs.lat := point_lattice;
     ValueAbs.top := PTop;
     ValueAbs.op_c := fun z _ => Cost.step ;; Cost.ret (PVal z);
     ValueAbs.back_c := fun _ _ xs => Cost.ret xs;
     ValueAbs.guard_c := fun z xs => map_c (fun a => meet a (PVal z)) xs |}.

Definition sem : ValueSem.t Z Z Z :=
  {| ValueSem.eval := fun z _ => Some z;
     ValueSem.holds := fun z cs => Forall (fun c => c = z) cs |}.

Lemma meet_sound a b c :
  gamma gam a c -> gamma gam b c -> gamma gam (Cost.value (meet a b)) c.
Proof.
  change (point_gamma 1%positive a c -> point_gamma 1%positive b c ->
    point_gamma 1%positive (point_meet a b) c).
  destruct a as [|x|], b as [|y|]; cbn [point_gamma point_meet];
    intros Ha Hb; try contradiction; try exact I; try assumption.
  subst x y. now rewrite Z.eqb_refl.
Qed.

Lemma greatest a : leb (ValueAbs.lat values) a (ValueAbs.top values) = true.
Proof.
  destruct a; reflexivity.
Qed.

(** Open integer points inhabit every value-law obligation without a Bits language parameter. *)
Theorem value_laws_fixture : value_laws values sem gam.
Proof.
  constructor.
  - exact point_lattice_laws.
  - constructor. intros [|x|] [|y|] c Hle Ha; try contradiction; try discriminate;
      try exact I.
    change (Z.eqb x y = true) in Hle. apply Z.eqb_eq in Hle.
    cbn [gam gamma point_gamma] in *. congruence.
  - intros c Hbot. exact Hbot.
  - intros c. exact I.
  - intros k fs cs c Hfacts Heval. injection Heval as <-. reflexivity.
  - intros k a fs cs c Hfacts Heval Ha. exact Hfacts.
  - intros z fs cs Hfacts Hguard.
    change (Forall2 (gamma gam)
      (Cost.value (map_c (fun a => meet a (PVal z)) fs)) cs).
    rewrite value_map_c. induction Hfacts as [|a c fs cs Ha Htail IH];
      inversion Hguard as [|c' cs' Hc Hcs]; subst; cbn [map]; constructor.
    + apply meet_sound; [exact Ha|reflexivity].
    + apply IH. exact Hcs.
  - intros k a fs. reflexivity.
  - intros z fs. change (length (Cost.value (map_c (fun a => meet a (PVal z)) fs)) =
      length fs).
    rewrite value_map_c, length_map. reflexivity.
Qed.

Definition SD := StateEnv.state bool_encoding values meet.
Definition RD := StateEnv.relational bool_encoding values meet.
Definition gs := env_concretisation bool_encoding values gam.
Definition empty : StateEnv.t bool_encoding point := Some (env_empty bool_encoding).
Definition stored xs : StateEnv.t bool_encoding point := Some (env_of_list bool_encoding xs).
Definition get x s := StateAbs.project SD x s.

(** The two-variable environment inhabits all state laws, including distinct-variable updates. *)
Theorem state_laws_fixture :
  state_laws SD sem (StateEnv.semantics bool_encoding) gam gs.
Proof.
  apply env_state_laws; [exact bool_encoding_laws|exact value_laws_fixture|
    exact greatest|exact meet_sound].
Qed.

(** One reached state describes genuinely different values at the two coordinates. *)
Example two_variable_control :
  gamma gs (stored [(false, PVal 1); (true, PVal 2)])
    (fun x => if x then 2%Z else 1%Z).
Proof.
  intros []; vm_compute; reflexivity.
Qed.

Example constant_assignment :
  get false (StateAbs.assign SD false (Node 7 []) empty) = PVal 7.
Proof. vm_compute. reflexivity. Qed.

Example copy_assignment :
  get true (StateAbs.assign SD true (Leaf false) (stored [(false, PVal 7)])) = PVal 7.
Proof. vm_compute. reflexivity. Qed.

Example distinct_variable_frame :
  get true (StateAbs.assign SD false (Node 9 []) (stored [(true, PVal 2)])) = PVal 2.
Proof. vm_compute. reflexivity. Qed.

Example havoc_replaces_binding :
  get false (StateAbs.havoc SD false (stored [(false, PVal 7)])) = PTop.
Proof. vm_compute. reflexivity. Qed.

Example havoc_both_concrete_replacements :
  (StateSem.update (StateEnv.semantics bool_encoding) false 3%Z
    (fun _ => 1%Z) false,
   StateSem.update (StateEnv.semantics bool_encoding) false 8%Z
    (fun _ => 1%Z) false) = (3%Z, 8%Z).
Proof. vm_compute. reflexivity. Qed.

Example impossible_assume :
  get false (StateAbs.assume SD 1 [Leaf false] (stored [(false, PVal 0)])) = PBot.
Proof. vm_compute. reflexivity. Qed.

Example two_term_refinement :
  let s := StateAbs.assume SD 4 [Leaf false; Leaf true] empty in
  (get false s, get true s) = (PVal 4, PVal 4).
Proof. vm_compute. reflexivity. Qed.

Example nested_term_materialization :
  let s := StateAbs.assume SD 7 [Node 7 [Leaf false]; Leaf true]
    (stored [(false, PVal 3)]) in
  (get false s, get true s) = (PVal 3, PVal 7).
Proof. vm_compute. reflexivity. Qed.

Example duplicate_leaf_meets_threaded_values :
  get false (StateAbs.assume SD 4 [Leaf false; Leaf false] empty) = PVal 4.
Proof. vm_compute. reflexivity. Qed.

Example different_key_join :
  let s := join (StateAbs.lat SD) (stored [(false, PVal 1)]) (stored [(true, PVal 2)]) in
  (get false s, get true s) = (PTop, PTop).
Proof. vm_compute. reflexivity. Qed.

Example absent_and_empty_mean_top : (get false empty, get true empty) = (PTop, PTop).
Proof. vm_compute. reflexivity. Qed.

Example fresh_bottom_is_distinct :
  (leb (StateAbs.lat SD) None empty, leb (StateAbs.lat SD) empty None) = (true, false).
Proof. vm_compute. reflexivity. Qed.

Example fresh_bottom_survives_transfers :
  (StateAbs.assign SD false (Node 1 []) None,
   StateAbs.havoc SD false None, StateAbs.assume SD 1 [Leaf false] None) =
    (None, None, None).
Proof. vm_compute. reflexivity. Qed.

Example empty_guard_keeps_old_binding :
  get true (StateAbs.assume SD 8 [] (stored [(true, PVal 2)])) = PVal 2.
Proof. vm_compute. reflexivity. Qed.

Example three_widening_iterations :
  let s1 := widen (StateAbs.lat SD) None (stored [(false, PVal 1)]) in
  let s2 := widen (StateAbs.lat SD) s1 (stored [(false, PVal 2)]) in
  let s3 := widen (StateAbs.lat SD) s2 empty in
  (get false s1, get false s2, get false s3) = (PVal 1, PTop, PTop).
Proof. vm_compute. reflexivity. Qed.

(** Point widening satisfies its default equation despite left-preserving narrowing. *)
Example widening_only_compatibility :
  forall a b,
    env_default PTop (env_optional Top_default PTop point_lattice Env_widen a b) =
    widen point_lattice (env_default PTop a) (env_default PTop b).
Proof.
  intros [[|x|]|] [[|y|]|]; reflexivity.
Qed.

(** Ordinary point narrowing cannot satisfy the stronger full optional/default contract. *)
Example full_narrowing_compatibility_rejected :
  ~ env_default_laws Top_default PTop point_lattice.
Proof.
  intro H. pose proof (env_optional_exact H Env_narrow None (Some (PVal 1))) as Heq.
  discriminate Heq.
Qed.

Example widening_observation_without_narrowing :
  forall x s r, StateEnv.observe bool_encoding values x (widen (StateAbs.lat SD) s r) =
    widen (lift_bot point_lattice)
      (StateEnv.observe bool_encoding values x s) (StateEnv.observe bool_encoding values x r).
Proof.
  apply env_widen_pointwise. exact widening_only_compatibility.
Qed.

Example empty_key_fresh_bottom_has_empty_meaning :
  forall st : Empty_set -> Z,
    ~ gamma (env_concretisation (BaseEncoding.of_pure (fun x : Empty_set => match x with end))
      values gam) None st.
Proof.
  intros st Hbot. exact Hbot.
Qed.

Example empty_key_reached_map_has_full_meaning :
  forall st : Empty_set -> Z,
    gamma (env_concretisation (BaseEncoding.of_pure (fun x : Empty_set => match x with end))
      values gam) (Some (env_empty _)) st.
Proof.
  intros st [].
Qed.

Definition costly_meet a b := Cost.tick 11 ;; meet a b.

Definition costly_values : ValueAbs.t point Z Z :=
  {| ValueAbs.lat := ValueAbs.lat values;
     ValueAbs.top := ValueAbs.top values;
     ValueAbs.op_c := ValueAbs.op_c values;
     ValueAbs.back_c := ValueAbs.back_c values;
     ValueAbs.guard_c := fun g xs => Cost.tick 17 ;; ValueAbs.guard_c values g xs |}.

Example guard_callback_charge_is_retained :
  Cost.ticks (StateEnv.assume_c bool_encoding costly_values meet 4
    [Leaf false; Leaf true] empty) =
  (Cost.ticks (StateEnv.assume_c bool_encoding values meet 4%Z
    [Leaf false; Leaf true] empty) + 17)%N.
Proof. vm_compute. reflexivity. Qed.

Example deferred_meet_charge_is_retained :
  Cost.ticks (StateEnv.assume_c bool_encoding values costly_meet 4
    [Leaf false; Leaf true] empty) =
  (Cost.ticks (StateEnv.assume_c bool_encoding values meet 4%Z
    [Leaf false; Leaf true] empty) + 22)%N.
Proof. vm_compute. reflexivity. Qed.

Example materialization_charges_each_actual_lookup :
  Cost.ticks (StateEnv.materialize_c bool_encoding [false; true; false]
    (fun _ => Cost.tick 13 ;; Cost.ret PTop) (env_empty bool_encoding)) =
  (Cost.ticks (StateEnv.materialize_c bool_encoding [false; true; false]
    (fun _ => Cost.ret PTop) (env_empty bool_encoding)) + 39)%N.
Proof. vm_compute. reflexivity. Qed.

Example support_traversal_charge :
  Cost.ticks (StateEnv.supports_c [Node 7 [Leaf false; Leaf true]; Leaf false]) = 13%N.
Proof. vm_compute. reflexivity. Qed.

Example environment_read_charge_is_retained :
  Cost.ticks (abs_eval_c values (StateEnv.read_c bool_encoding values
    (env_of_list bool_encoding [(false, PVal 3)])) (Leaf false)) =
  (Cost.ticks (StateEnv.read_c bool_encoding values
    (env_of_list bool_encoding [(false, PVal 3)]) false) + 2)%N.
Proof. vm_compute. reflexivity. Qed.

Example equality_charge_is_retained :
  let f := Cost.value (abs_assume_c (fun x y =>
    Cost.tick 19 ;; eqb_c bool_encoding x y) meet values
    (fun _ => Cost.ret PTop) (Leaf false) (PVal 4)) in
  let g := Cost.value (abs_assume_c (eqb_c bool_encoding) meet values
    (fun _ => Cost.ret PTop) (Leaf false) (PVal 4)) in
  Cost.ticks (f true) = (Cost.ticks (g true) + 19)%N.
Proof. vm_compute. reflexivity. Qed.

End EnvFixture.

Module AssumptionOrder.

(** This computational probe records order without asserting semantic value laws. *)
Definition values : ValueAbs.t (list nat) unit (list (list nat)) :=
  {| ValueAbs.lat := simple (fun _ _ => true) [] (fun a _ => a);
     ValueAbs.top := [];
     ValueAbs.op_c := fun _ _ => Cost.ret [];
     ValueAbs.back_c := fun _ _ _ => Cost.ret [[1%nat]; [2%nat]];
     ValueAbs.guard_c := fun targets _ => Cost.ret targets |}.

Definition SD := StateEnv.state bool_encoding values (@app_c nat).
Definition input : StateEnv.t bool_encoding (list nat) :=
  Some (env_of_list bool_encoding [(false, [9%nat]); (true, [8%nat])]).

Example term_order_survives_materialization :
  StateAbs.project SD false
    (StateAbs.assume SD [[1%nat]; [2%nat]] [Leaf false; Leaf false] input) =
    [9%nat; 1%nat; 2%nat].
Proof. vm_compute. reflexivity. Qed.

Example reversing_guard_targets_is_observable :
  StateAbs.project SD false
    (StateAbs.assume SD [[2%nat]; [1%nat]] [Leaf false; Leaf false] input) =
    [9%nat; 2%nat; 1%nat].
Proof. vm_compute. reflexivity. Qed.

Example generic_node_order_survives_materialization :
  StateAbs.project SD false
    (StateAbs.assume SD [[]] [Node tt [Leaf false; Leaf false]] input) =
    [9%nat; 1%nat; 2%nat].
Proof. vm_compute. reflexivity. Qed.

Example materialization_does_not_recompute_old_bindings :
  StateAbs.project SD true
    (StateAbs.assume SD [[1%nat]; [2%nat]] [Leaf false; Leaf false] input) = [8%nat].
Proof. vm_compute. reflexivity. Qed.

End AssumptionOrder.

Module TopOrderBoundary.

Inductive fact :=
  | Bot
  | Point
  | Upper.

Definition le (a b : fact) :=
  match a, b with
  | Bot, _ => true
  | _, Upper => true
  | Point, Point => true
  | _, _ => false
  end.

Definition sup (a b : fact) :=
  match a, b with
  | Bot, _ => b
  | _, Bot => a
  | Point, Point => Point
  | _, _ => Upper
  end.

Definition L := simple le Bot sup.
Definition gam : concretisation fact unit :=
  {| gamma := fun a _ => match a with Bot => False | _ => True end |}.
Definition values : ValueAbs.t fact unit unit :=
  {| ValueAbs.lat := L;
     ValueAbs.top := Point;
     ValueAbs.op_c := fun _ _ => Cost.ret Point;
     ValueAbs.back_c := fun _ _ xs => Cost.ret xs;
     ValueAbs.guard_c := fun _ xs => Cost.ret xs |}.
Definition sem : ValueSem.t unit unit unit :=
  {| ValueSem.eval := fun _ _ => Some tt;
     ValueSem.holds := fun _ _ => True |}.

(** Semantic fullness does not force the selected top value to be greatest in the order. *)
Example semantic_value_laws : value_laws values sem gam.
Proof.
  assert (HL : lattice_laws L).
  { apply simple_laws.
    - intros []; reflexivity.
    - intros [] [] [] Hxy Hyz; discriminate || reflexivity.
    - intros []; reflexivity.
    - intros [] []; reflexivity.
    - intros [] []; reflexivity. }
  constructor.
  - exact HL.
  - constructor. intros [] [] [] Hle Ha; try discriminate; try contradiction; exact I.
  - intros [] Hbot. exact Hbot.
  - intros []. exact I.
  - intros k fs cs [] Hfacts Heval. exact I.
  - intros k a fs cs c Hfacts Heval Ha. exact Hfacts.
  - intros g fs cs Hfacts Hguard. exact Hfacts.
  - intros. reflexivity.
  - intros. reflexivity.
Qed.

Definition SL := StateEnv.lat bool_encoding values.
Definition upper := Some (env_of_list bool_encoding [(false, Upper)]).
Definition empty := Some (@env_empty bool fact bool_encoding).
Definition point := Some (env_of_list bool_encoding [(false, Point)]).

Example top_order_premise_is_not_semantic_fullness :
  leb (ValueAbs.lat values) Upper (ValueAbs.top values) = false.
Proof. vm_compute. reflexivity. Qed.

Example missing_top_order_breaks_transitivity :
  (leb SL upper empty, leb SL empty point, leb SL upper point) = (true, true, false).
Proof. vm_compute. reflexivity. Qed.

End TopOrderBoundary.
