(** * Adjoining an unreachable bottom

    Option adds a fresh bottom while retaining reached values' component operations.
    For example, joining [None] and [Some a] returns [Some a].
    Builds on: CostMonad, LatticeCore, LatticeHeight, LatticeConcrete and LatticeTactics. *)

From Stdlib Require Import Bool Arith NArith Lia.
From Galois.Cost Require Import CostMonad CostTactics.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeConcrete LatticeTactics.
Import Cost.Notations.

(** Lifted operations charge a case step and one tick for each underlying callback call. *)
Definition lift_bot {A} (L : lattice A) : lattice (option A) :=
  {| leb_c := fun x y => Cost.step ;;
       match x, y with
       | None, _ => Cost.ret true
       | Some a, Some b => Cost.step ;; leb_c L a b
       | Some _, None => Cost.ret false
       end;
     join_c := fun x y => Cost.step ;;
       match x, y with
       | None, _ => Cost.ret y
       | _, None => Cost.ret x
       | Some a, Some b => Cost.step ;; Cost.map Some (join_c L a b)
       end;
     widen_c := fun x y => Cost.step ;;
       match x, y with
       | None, _ => Cost.ret y
       | _, None => Cost.ret x
       | Some a, Some b => Cost.step ;; Cost.map Some (widen_c L a b)
       end;
     narrow_c := fun x y => Cost.step ;;
       match x, y with
       | None, _ => Cost.ret None
       | _, None => Cost.ret x
       | Some a, Some b => Cost.step ;; Cost.map Some (narrow_c L a b)
       end;
     bot := None |}.

(** Lifted comparison makes None least and compares reached values in the component. *)
Theorem leb_lift_bot {A} (L : lattice A) x y :
  leb (lift_bot L) x y =
  match x, y with
  | None, _ => true
  | Some a, Some b => leb L a b
  | Some _, None => false
  end.
Proof.
  destruct x, y; reflexivity.
Qed.

(** Lifted join ignores the unreachable input and joins two reached values. *)
Theorem join_lift_bot {A} (L : lattice A) x y :
  join (lift_bot L) x y =
  match x, y with
  | None, _ => y
  | _, None => x
  | Some a, Some b => Some (join L a b)
  end.
Proof.
  destruct x, y; reflexivity.
Qed.

(** Lifted widening ignores the unreachable input and widens two reached values. *)
Theorem widen_lift_bot {A} (L : lattice A) x y :
  widen (lift_bot L) x y =
  match x, y with
  | None, _ => y
  | _, None => x
  | Some a, Some b => Some (widen L a b)
  end.
Proof.
  destruct x, y; reflexivity.
Qed.

(** Lifted narrowing keeps the left input when the right input is unreachable. *)
Theorem narrow_lift_bot {A} (L : lattice A) x y :
  narrow (lift_bot L) x y =
  match x, y with
  | None, _ => None
  | _, None => x
  | Some a, Some b => Some (narrow L a b)
  end.
Proof.
  destruct x, y; reflexivity.
Qed.

(** Lifted meanings assign the empty meaning to the fresh bottom. *)
Definition lift_bot_gamma {A C} (G : concretisation A C) : concretisation (option A) C :=
  {| gamma := fun a c =>
       match a with
       | None => False
       | Some v => gamma G v c
       end |}.

(** Lifted agreement imposes no condition at the fresh bottom. *)
Definition lift_bot_agree {A C} (R : agreement A C) : agreement (option A) C :=
  {| agree := fun a x y =>
       match a with
       | None => True
       | Some v => agree R v x y
       end |}.

(** The lifted invariant includes None and requires the component invariant at Some. *)
Definition lift_bot_inv {A} (inv : A -> Prop) (a : option A) : Prop :=
  match a with
  | None => True
  | Some v => inv v
  end.

(** Lifted callbacks add at most two ticks to the component bound on reached inputs. *)
Theorem lift_bot_cost {A} (L : lattice A) inv k :
  cost_bounded_on L inv k ->
  cost_bounded_on (lift_bot L) (lift_bot_inv inv) (k + 2)%N.
Proof.
  intros H [a |] [b |] Ha Hb; cbn [lift_bot_inv] in *;
    cbn [lift_bot leb_c join_c widen_c narrow_c]; cost_simpl.
  - destruct (H a b Ha Hb) as [Hle [Hjoin [Hwiden Hnarrow]]]; repeat split; lia.
  - repeat split; lia.
  - repeat split; lia.
  - repeat split; lia.
Qed.

(** This local normalization exposes only the option equations and constructor matches. *)
Local Ltac lift_reduce :=
  repeat first
    [ rewrite join_lift_bot
    | rewrite widen_lift_bot
    | rewrite narrow_lift_bot
    | rewrite leb_lift_bot ];
  cbn beta iota.

Section Lift.
Context {A : Type} (L : lattice A).

(** Adjoining a fresh bottom preserves all nine weak laws. *)
Theorem lift_bot_laws : lattice_laws L -> lattice_laws (lift_bot L).
Proof.
  intro H; constructor.
  - intros [a |]; lift_reduce; try reflexivity; order_solver.
  - intros [a |] [b |] [c |]; lift_reduce; intros Hab Hbc;
      try discriminate; try reflexivity; order_solver.
  - intros [a |]; reflexivity.
  - intros [a |] [b |]; lift_reduce; try reflexivity; order_solver.
  - intros [a |] [b |]; lift_reduce; try reflexivity; order_solver.
  - intros [a |] [b |]; lift_reduce; try reflexivity; order_solver.
  - intros [a |] [b |]; lift_reduce; try reflexivity; order_solver.
  - intros [a |] [b |]; lift_reduce; intro Hle;
      try discriminate; try reflexivity; order_solver.
  - intros [a |] [b |]; lift_reduce; intro Hle;
      try discriminate; try reflexivity; order_solver.
Qed.

(** Adjoining bottom preserves least joins. *)
Theorem lift_bot_lub : lub_laws L -> lub_laws (lift_bot L).
Proof.
  intro H; constructor; intros [a |] [b |] [c |]; lift_reduce; intros Ha Hb;
    try discriminate; try reflexivity; try assumption; apply (join_least H); assumption.
Qed.

(** The reached component top bounds all lifted values. *)
Definition lift_bot_top (T : top L) : top (lift_bot L).
Proof.
  refine {| top_value := Some (top_value T) |}; intros [a |]; lift_reduce.
  - apply (top_greatest T).
  - reflexivity.
Defined.

(** Invariant closure lifts without requiring the component bottom to be reached. *)
Theorem lift_bot_closed {inv} : closed_on L inv ->
  closed_on (lift_bot L) (lift_bot_inv inv).
Proof.
  intro C; constructor; [exact I | | |].
  - intros [a |] [b |] Ha Hb; rewrite join_lift_bot; cbn [lift_bot_inv] in *;
      try assumption; apply (join_inv C); assumption.
  - intros [a |] [b |] Ha Hb; rewrite widen_lift_bot; cbn [lift_bot_inv] in *;
      try assumption; apply (widen_inv C); assumption.
  - intros [a |] [b |] Ha Hb Hle; rewrite narrow_lift_bot;
      rewrite leb_lift_bot in Hle; cbn [lift_bot_inv] in *; try assumption.
    apply (narrow_inv C); assumption.
Qed.

(** Reached heights add one above the fresh bottom's zero rank. *)
Theorem lift_bot_height {inv} (H : lattice_laws L) (R : height_on L inv) :
    height_on (lift_bot L) (lift_bot_inv inv).
Proof.
  refine {| rank := fun x =>
              match x with
              | None => 0
              | Some a => S (rank R a)
              end;
            bound := S (bound R) |}.
  - intros [a |] Ha; cbn [lift_bot_inv] in *.
    + pose proof (rank_bounded R a Ha); lia.
    + lia.
  - intros [a |] [b |] Ha Hb Hle; rewrite leb_lift_bot in Hle;
      cbn [lift_bot_inv] in *; try discriminate; try lia.
    pose proof (rank_monotone R a b Ha Hb Hle); lia.
  - intros [a |] [b |] Ha Hb Hstrict; rewrite join_lift_bot in *;
      rewrite leb_lift_bot in Hstrict; cbn [lift_bot_inv] in *;
      try discriminate; try lia.
    + pose proof (join_rank_grows R a b Ha Hb Hstrict); lia.
    + rewrite (leb_refl H) in Hstrict; discriminate.
Defined.

(** The fresh bottom receives one credit above the component widening bound. *)
Theorem lift_bot_wrank {inv} (W : widening_rank_on L inv) :
    widening_rank_on (lift_bot L) (lift_bot_inv inv).
Proof.
  refine {| wrank := fun x =>
              match x with
              | None => S (wbound W)
              | Some a => wrank W a
              end;
            wbound := S (wbound W) |}.
  - intros [a |] Ha; cbn [lift_bot_inv] in *.
    + pose proof (wrank_bounded W a Ha); lia.
    + lia.
  - intros [a |] [b |] Ha Hb Hle; rewrite widen_lift_bot;
      rewrite leb_lift_bot in Hle; cbn [lift_bot_inv] in *;
      try discriminate; try lia; apply (widen_rank_stable W); assumption.
  - intros [a |] [b |] Ha Hb Hstrict; rewrite widen_lift_bot;
      rewrite leb_lift_bot in Hstrict; cbn [lift_bot_inv] in *; try discriminate.
    + apply (widen_rank_progress W); assumption.
    + pose proof (wrank_bounded W b Hb); lia.
Defined.

Context {C : Type} (G : concretisation A C) (R : agreement A C).

(** The lifted meaning is monotone when the component meaning is monotone. *)
Theorem lift_bot_gamma_laws : concretisation_laws L G ->
  concretisation_laws (lift_bot L) (lift_bot_gamma G).
Proof.
  intro HG; constructor; intros [a |] [b |] c Hle Hc;
    rewrite leb_lift_bot in Hle; cbn [lift_bot_gamma gamma] in *;
    try contradiction; try discriminate; eapply (gamma_monotone HG); eassumption.
Qed.

(** The fresh bottom has empty meaning independently of the component's bottom. *)
Theorem lift_bot_bot_empty : bottom_empty (lift_bot L) (lift_bot_gamma G).
Proof.
  constructor; intros c Hc; exact Hc.
Qed.

(** A full component top remains full after lifting. *)
Theorem lift_bot_top_full (T : top L) :
  top_full T G -> top_full (lift_bot_top T) (lift_bot_gamma G).
Proof.
  intro HG; constructor; intro c; apply (gamma_top_full HG).
Qed.

(** Lifted agreement is reflexive and antitone when component agreement is. *)
Theorem lift_bot_agree_laws : agreement_laws L R ->
  agreement_laws (lift_bot L) (lift_bot_agree R).
Proof.
  intro HR; constructor.
  - intros [a |] c; cbn [lift_bot_agree agree]; [apply (agree_refl HR) | exact I].
  - intros [a |] [b |] x y Hle Hxy; rewrite leb_lift_bot in Hle;
      cbn [lift_bot_agree agree] in *; try discriminate; try exact I.
    eapply (agree_antitone HR); eassumption.
Qed.

(** The fresh bottom needs no agreement information. *)
Theorem lift_bot_agree_bot : agreement_bot (lift_bot L) (lift_bot_agree R).
Proof.
  constructor; intros; exact I.
Qed.

(** Component join agreement extends across the fresh bottom. *)
Theorem lift_bot_agree_join : agreement_join_law L R ->
  agreement_join_law (lift_bot L) (lift_bot_agree R).
Proof.
  intro HR; constructor; intros [a |] [b |] x y Hx Hy; rewrite join_lift_bot;
    cbn [lift_bot_agree agree] in *; try assumption; apply (agree_join HR); assumption.
Qed.
End Lift.
