(** * Adjoining an unknown top

    A top lift adds a fresh value above an existing lattice.
    For example, joining [Unknown] with any element gives [Unknown].
    Builds on: CostMonad, LatticeCore, LatticeHeight and LatticeConcrete. *)

From Stdlib Require Import Bool Arith NArith Lia.
From Galois.Cost Require Import CostMonad CostTactics.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeConcrete LatticeTactics.
Import Cost.Notations.
Local Open Scope nat_scope.

(** An element is either reached in the component or fully unknown. *)
Inductive lift_top (A : Type) : Type :=
  | Elem (a : A)
  | Unknown.

Arguments Elem {A}.
Arguments Unknown {A}.

(** Top-lifted callbacks charge their cases and component callback invocations. *)
Definition lift_top_lattice {A} (L : lattice A) : lattice (lift_top A) :=
  {| leb_c := fun x y => Cost.step ;;
       match x, y with
       | _, Unknown => Cost.ret true
       | Elem a, Elem b => Cost.step ;; leb_c L a b
       | Unknown, Elem _ => Cost.ret false
       end;
     join_c := fun x y => Cost.step ;;
       match x, y with
       | Elem a, Elem b => Cost.step ;; Cost.map Elem (join_c L a b)
       | _, _ => Cost.ret Unknown
       end;
     widen_c := fun x y => Cost.step ;;
       match x, y with
       | Elem a, Elem b => Cost.step ;; Cost.map Elem (widen_c L a b)
       | _, _ => Cost.ret Unknown
       end;
     narrow_c := fun x y => Cost.step ;;
       match x, y with
       | Elem a, Elem b => Cost.step ;; Cost.map Elem (narrow_c L a b)
       | Unknown, _ => Cost.ret y
       | _, Unknown => Cost.ret x
       end;
     bot := Elem (bot L) |}.

(** Comparison delegates between elements and makes Unknown greatest. *)
Theorem leb_lift_top {A} (L : lattice A) x y :
  leb (lift_top_lattice L) x y =
  match x, y with
  | _, Unknown => true
  | Elem a, Elem b => leb L a b
  | Unknown, Elem _ => false
  end.
Proof.
  destruct x, y; reflexivity.
Qed.

(** Joining two elements delegates, and Unknown absorbs the join. *)
Theorem join_lift_top {A} (L : lattice A) x y :
  join (lift_top_lattice L) x y =
  match x, y with
  | Elem a, Elem b => Elem (join L a b)
  | _, _ => Unknown
  end.
Proof.
  destruct x, y; reflexivity.
Qed.

(** Widening two elements delegates, and Unknown absorbs widening. *)
Theorem widen_lift_top {A} (L : lattice A) x y :
  widen (lift_top_lattice L) x y =
  match x, y with
  | Elem a, Elem b => Elem (widen L a b)
  | _, _ => Unknown
  end.
Proof.
  destruct x, y; reflexivity.
Qed.

(** Narrowing Unknown descends to the second argument. *)
Theorem narrow_lift_top {A} (L : lattice A) x y :
  narrow (lift_top_lattice L) x y =
  match x, y with
  | Elem a, Elem b => Elem (narrow L a b)
  | Unknown, _ => y
  | _, Unknown => x
  end.
Proof.
  destruct x, y; reflexivity.
Qed.

(** The lifted invariant includes Unknown. *)
Definition lift_top_inv {A} (inv : A -> Prop) (x : lift_top A) : Prop :=
  match x with
  | Elem a => inv a
  | Unknown => True
  end.

(** Unknown denotes every concrete value. *)
Definition lift_top_gamma {A C} (G : concretisation A C) : concretisation (lift_top A) C :=
  {| gamma := fun x c =>
       match x with
       | Elem a => gamma G a c
       | Unknown => True
       end |}.

(** Unknown agreement requires equality. *)
Definition lift_top_agree {A C} (R : agreement A C) : agreement (lift_top A) C :=
  {| agree := fun a x y =>
       match a with
       | Elem v => agree R v x y
       | Unknown => x = y
       end |}.

(** This normalization exposes only the lifted operation equations. *)
Local Ltac lift_top_reduce :=
  repeat first
    [ rewrite join_lift_top
    | rewrite widen_lift_top
    | rewrite narrow_lift_top
    | rewrite leb_lift_top ];
  cbn beta iota.

Section Lift.
Context {A : Type} (L : lattice A).

(** Adjoining top preserves weak lattice laws. *)
Theorem lift_top_laws : lattice_laws L -> lattice_laws (lift_top_lattice L).
Proof.
  intro H; constructor.
  - intros [a |]; lift_top_reduce; try reflexivity; order_solver.
  - intros [a |] [b |] [c |]; lift_top_reduce; intros Hab Hbc;
      try discriminate; try reflexivity; order_solver.
  - intro x; change (leb (lift_top_lattice L) (Elem (bot L)) x = true).
    destruct x as [a |]; lift_top_reduce; try reflexivity; order_solver.
  - intros [a |] [b |]; lift_top_reduce; try reflexivity; order_solver.
  - intros [a |] [b |]; lift_top_reduce; try reflexivity; order_solver.
  - intros [a |] [b |]; lift_top_reduce; try reflexivity; order_solver.
  - intros [a |] [b |]; lift_top_reduce; try reflexivity; order_solver.
  - intros [a |] [b |]; lift_top_reduce; intro Hle;
      try discriminate; try reflexivity; order_solver.
  - intros [a |] [b |]; lift_top_reduce; intro Hle;
      try discriminate; try reflexivity; order_solver.
Qed.

(** Adjoining top preserves least joins. *)
Theorem lift_top_lub : lub_laws L -> lub_laws (lift_top_lattice L).
Proof.
  intro H; constructor; intros [a |] [b |] [c |]; lift_top_reduce; intros Ha Hb;
    try discriminate; try reflexivity; apply (join_least H); assumption.
Qed.

(** Unknown is the top of the lifted lattice. *)
Definition lift_top_top : top (lift_top_lattice L).
Proof.
  refine {| top_value := Unknown |}; intros [a |]; reflexivity.
Defined.

(** Component closure extends to the lifted invariant. *)
Theorem lift_top_closed {inv} : closed_on L inv ->
  closed_on (lift_top_lattice L) (lift_top_inv inv).
Proof.
  intro C; constructor.
  - exact (bot_inv C).
  - intros [a |] [b |] Ha Hb; rewrite join_lift_top; cbn [lift_top_inv] in *;
      try exact I; apply (join_inv C); assumption.
  - intros [a |] [b |] Ha Hb; rewrite widen_lift_top; cbn [lift_top_inv] in *;
      try exact I; apply (widen_inv C); assumption.
  - intros [a |] [b |] Ha Hb Hle; rewrite narrow_lift_top;
      rewrite leb_lift_top in Hle; cbn [lift_top_inv] in *; try assumption.
    apply (narrow_inv C); assumption.
Qed.

(** Unknown receives a rank above the component height bound. *)
Theorem lift_top_height {inv} (H : height_on L inv) :
  height_on (lift_top_lattice L) (lift_top_inv inv).
Proof.
  refine {| rank := fun x =>
              match x with
              | Elem a => rank H a
              | Unknown => S (bound H)
              end;
            bound := S (bound H) |}.
  - intros [a |] Ha; cbn [lift_top_inv] in *.
    + pose proof (rank_bounded H a Ha); lia.
    + lia.
  - intros [a |] [b |] Ha Hb Hle; rewrite leb_lift_top in Hle;
      cbn [lift_top_inv] in *; try discriminate; try lia.
    + apply (rank_monotone H); assumption.
    + pose proof (rank_bounded H a Ha); lia.
  - intros [a |] [b |] Ha Hb Hstrict; rewrite join_lift_top in *;
      rewrite leb_lift_top in Hstrict; cbn [lift_top_inv] in *;
      try discriminate.
    + apply (join_rank_grows H); assumption.
    + pose proof (rank_bounded H a Ha); lia.
Defined.

(** Unknown has zero widening credit, below every component credit. *)
Theorem lift_top_wrank {inv} (W : widening_rank_on L inv) :
  widening_rank_on (lift_top_lattice L) (lift_top_inv inv).
Proof.
  refine {| wrank := fun x =>
              match x with
              | Elem a => S (wrank W a)
              | Unknown => 0
              end;
            wbound := S (wbound W) |}.
  - intros [a |] Ha; cbn [lift_top_inv] in *.
    + pose proof (wrank_bounded W a Ha); lia.
    + lia.
  - intros [a |] [b |] Ha Hb Hle; rewrite widen_lift_top;
      rewrite leb_lift_top in Hle; cbn [lift_top_inv] in *;
      try discriminate; try lia.
    pose proof (widen_rank_stable W a b Ha Hb Hle); lia.
  - intros [a |] [b |] Ha Hb Hstrict; rewrite widen_lift_top;
      rewrite leb_lift_top in Hstrict; cbn [lift_top_inv] in *;
      try discriminate; try lia.
    pose proof (widen_rank_progress W a b Ha Hb Hstrict); lia.
Defined.

Context {C : Type} (G : concretisation A C) (R : agreement A C).

(** Component monotonicity implies lifted meaning monotonicity. *)
Theorem lift_top_gamma_laws : concretisation_laws L G ->
  concretisation_laws (lift_top_lattice L) (lift_top_gamma G).
Proof.
  intro HG; constructor; intros [a |] [b |] c Hle Hc;
    rewrite leb_lift_top in Hle; cbn [lift_top_gamma gamma] in *;
    try discriminate; try exact I; eapply (gamma_monotone HG); eassumption.
Qed.

(** Component agreement laws extend to the fresh top. *)
Theorem lift_top_agree_laws : agreement_laws L R ->
  agreement_laws (lift_top_lattice L) (lift_top_agree R).
Proof.
  intro HR; constructor.
  - intros [a |] c; cbn [lift_top_agree agree]; [apply (agree_refl HR) | reflexivity].
  - intros [a |] [b |] x y Hle Hxy; rewrite leb_lift_top in Hle;
      cbn [lift_top_agree agree] in *; try discriminate; try exact Hxy.
    + eapply (agree_antitone HR); eassumption.
    + subst y; apply (agree_refl HR).
Qed.
End Lift.

(** Fresh top denotes every concrete value. *)
Theorem lift_top_full {A C} (L : lattice A) (G : concretisation A C) :
  top_full (lift_top_top L) (lift_top_gamma G).
Proof.
  constructor; intro c; exact I.
Qed.

(** An empty component bottom stays empty after adjoining top. *)
Theorem lift_top_bot_empty {A C} (L : lattice A) (G : concretisation A C) :
  bottom_empty L G -> bottom_empty (lift_top_lattice L) (lift_top_gamma G).
Proof.
  intro HG; constructor; apply (gamma_bot_empty HG).
Qed.

(** An agreement-free component bottom stays agreement-free after adjoining top. *)
Theorem lift_top_agree_bot {A C} (L : lattice A) (R : agreement A C) :
  agreement_bot L R -> agreement_bot (lift_top_lattice L) (lift_top_agree R).
Proof.
  intro HR; constructor; apply (agree_bot HR).
Qed.

(** Top-lifted joins preserve agreement, including the absorbing equality cases. *)
Theorem lift_top_agree_join {A C} (L : lattice A) (R : agreement A C) :
  agreement_join_law L R ->
  agreement_join_law (lift_top_lattice L) (lift_top_agree R).
Proof.
  intro HR; constructor; intros [a |] [b |] x y Ha Hb; rewrite join_lift_top;
    cbn [lift_top_agree agree] in *; try assumption.
  apply (agree_join HR); assumption.
Qed.

(** Top-lifted operations charge at most two ticks beyond the component bound. *)
Theorem lift_top_cost {A} (L : lattice A) inv k :
  cost_bounded_on L inv k ->
  cost_bounded_on (lift_top_lattice L) (lift_top_inv inv) (k + 2)%N.
Proof.
  intros K [a |] [b |] Ha Hb; cbn [lift_top_inv] in *;
    cbn [lift_top_lattice leb_c join_c widen_c narrow_c]; cost_simpl;
    try (repeat split; lia).
  destruct (K a b Ha Hb) as [Hl [Hj [Hw Hn]]]; repeat split; lia.
Qed.

Arguments lift_top_lattice {A} L : simpl never.
