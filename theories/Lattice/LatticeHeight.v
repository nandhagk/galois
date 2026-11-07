(** * Invariant-relative termination measures

    Heights count ascending joins and widening ranks count descending progress credits.
    For example, complementing a boolean height gives one credit at false.
    Builds on: LatticeCore. *)

From Stdlib Require Import Arith Lia.
From Galois.Lattice Require Import LatticeCore.

(** A monotone bounded rank grows on strict joins of invariant inputs. *)
Record height_on {A} (L : lattice A) (inv : A -> Prop) : Type := Height {
  rank : A -> nat;
  bound : nat;
  rank_bounded : forall a, inv a -> rank a <= bound;
  rank_monotone : forall a b, inv a -> inv b -> leb L a b = true -> rank a <= rank b;
  join_rank_grows : forall a b, inv a -> inv b -> leb L (join L a b) a = false ->
    rank a < rank (join L a b)
}.

(** A bounded widening rank decreases when the new input escapes the old input. *)
Record widening_rank_on {A} (L : lattice A) (inv : A -> Prop) : Type := WideningRank {
  wrank : A -> nat;
  wbound : nat;
  wrank_bounded : forall a, inv a -> wrank a <= wbound;
  widen_rank_stable : forall a b, inv a -> inv b -> leb L b a = true ->
    wrank (widen L a b) <= wrank a;
  widen_rank_progress : forall a b, inv a -> inv b -> leb L b a = false ->
    wrank (widen L a b) < wrank a
}.

Arguments rank {A L inv}.
Arguments bound {A L inv}.
Arguments rank_bounded {A L inv}.
Arguments rank_monotone {A L inv}.
Arguments join_rank_grows {A L inv}.
Arguments wrank {A L inv}.
Arguments wbound {A L inv}.
Arguments wrank_bounded {A L inv}.
Arguments widen_rank_stable {A L inv}.
Arguments widen_rank_progress {A L inv}.

(** Plain height applies to every carrier value. *)
Definition height {A} (L : lattice A) := height_on L (fun _ => True).

(** Plain widening rank applies to every carrier value. *)
Definition widening_rank {A} (L : lattice A) := widening_rank_on L (fun _ => True).

(** A widening rank never increases on invariant inputs. *)
Theorem widening_rank_nonincreasing {A} {L : lattice A} {inv}
    (W : widening_rank_on L inv) a b :
  inv a -> inv b -> wrank W (widen L a b) <= wrank W a.
Proof.
  intros Ha Hb; destruct (leb L b a) eqn:Hle.
  - apply (widen_rank_stable W a b Ha Hb Hle).
  - pose proof (widen_rank_progress W a b Ha Hb Hle); lia.
Qed.

(** Complementing height gives widening credits when widening equals join. *)
Theorem height_wrank {A} (L : lattice A) {inv}
    (Hlaws : lattice_laws L) (_Hlub : lub_laws L) (Hclosed : closed_on L inv)
    (Hw : forall a b, widen L a b = join L a b) (H : height_on L inv) :
    widening_rank_on L inv.
Proof.
  refine {| wrank := fun a => bound H - rank H a;
            wbound := bound H |}.
  - intros a Ha; lia.
  - intros a b Ha Hb _; rewrite Hw.
    pose proof (rank_monotone H a (join L a b) Ha (join_inv Hclosed a b Ha Hb)
      (join_upper_l Hlaws a b)); lia.
  - intros a b Ha Hb Hba; rewrite Hw.
    assert (Hstrict : leb L (join L a b) a = false).
    { destruct (leb L (join L a b) a) eqn:Hjoin; [| reflexivity].
      pose proof (leb_trans Hlaws _ _ _ (join_upper_r Hlaws a b) Hjoin) as Hcontra.
      rewrite Hba in Hcontra; discriminate. }
    pose proof (join_rank_grows H a b Ha Hb Hstrict).
    pose proof (rank_bounded H (join L a b) (join_inv Hclosed a b Ha Hb)); lia.
Defined.

(** Replacement widening needs fresh stable and progress proofs for its rank. *)
Definition with_widen_wrank {A} (L : lattice A) {inv} w
    (r : A -> nat) (b : nat)
    (Hb : forall a, inv a -> r a <= b)
    (Hs : forall a b, inv a -> inv b -> leb L b a = true -> r (w a b) <= r a)
    (Hp : forall a b, inv a -> inv b -> leb L b a = false -> r (w a b) < r a) :
    widening_rank_on (with_widen L w) inv :=
  @WideningRank A (with_widen L w) inv r b Hb Hs Hp.

(** Replacing widening leaves every height field valid because order and join are unchanged. *)
Definition with_widen_height {A} (L : lattice A) {inv} w (H : height_on L inv) :
    height_on (with_widen L w) inv :=
  @Height A (with_widen L w) inv (rank H) (bound H)
    (rank_bounded H) (rank_monotone H) (join_rank_grows H).

(** Replacing narrowing leaves every height field valid because order and join are unchanged. *)
Definition with_narrow_height {A} (L : lattice A) {inv} n (H : height_on L inv) :
    height_on (with_narrow L n) inv :=
  @Height A (with_narrow L n) inv (rank H) (bound H)
    (rank_bounded H) (rank_monotone H) (join_rank_grows H).
