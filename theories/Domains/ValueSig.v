(** * Value domains

    Value domains connect abstract transfers to a concrete operator language.
    For example, backward refinement retains operands that can produce the requested result.
    Builds on: LangSig and LatticeSig. *)

From Stdlib Require Import List ZArith.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig.

Module Type VALUE_DOMAIN_OPS (L : LANG_OPS).
  Include ALATTICE_OPS.
  Parameter forward : L.op -> list t -> t.
  Parameter backward : L.op -> t -> list t -> list t.
  Parameter guard : L.guard -> list t -> list t.
End VALUE_DOMAIN_OPS.

Module Type VALUE_DOMAIN_LAWS (L : LANG) (Import V : VALUE_DOMAIN_OPS L).
  (* spec: gamma *)
  Parameter gamma : t -> L.val -> Prop.
  (** Abstract inclusion entails concrete inclusion. *)
  Parameter gamma_mono : forall a b c, leb a b = true -> gamma a c -> gamma b c.
  (** Bottom describes no concrete value. *)
  Parameter gamma_bot : forall c, ~ gamma bot c.
  (** Top describes every concrete value. *)
  Parameter gamma_top : forall c, gamma top c.
  (** Meet retains values described by both operands. *)
  Parameter gamma_meet : forall a b c, gamma a c -> gamma b c -> gamma (meet a b) c.
  (** A positive bottom test excludes every concrete value. *)
  Parameter is_bot_sound : forall a c, is_bot a = true -> ~ gamma a c.
  (** Every value below a recognized bottom is recognized as bottom. *)
  Parameter is_bot_below : forall a b, leb a b = true -> is_bot b = true -> is_bot a = true.
  (** Forward transfer contains every successful concrete result. *)
  Parameter forward_sound : forall o xs cs c,
    Forall2 gamma xs cs -> L.eval o cs = Some c -> gamma (forward o xs) c.
  (** Backward transfer retains operands consistent with the abstract result. *)
  Parameter backward_sound : forall o r xs cs c,
    Forall2 gamma xs cs -> L.eval o cs = Some c -> gamma r c ->
    Forall2 gamma (backward o r xs) cs.
  (** Backward transfer refines each operand in its original position. *)
  Parameter backward_refines : forall o r xs,
    Forall2 (fun y x => leb y x = true) (backward o r xs) xs.
  (** Guard transfer retains operands satisfying the concrete guard. *)
  Parameter guard_sound : forall g xs cs,
    Forall2 gamma xs cs -> L.holds g cs -> Forall2 gamma (guard g xs) cs.
  (** Guard transfer refines each operand in its original position. *)
  Parameter guard_refines : forall g xs,
    Forall2 (fun y x => leb y x = true) (guard g xs) xs.
End VALUE_DOMAIN_LAWS.

Module Type VALUE_DOMAIN (L : LANG) :=
  VALUE_DOMAIN_OPS L <+ LATTICE_LAWS <+ HAS_TOP_LAWS <+ HAS_MEET_LOWER <+
  WIDENING_LAWS <+ VALUE_DOMAIN_LAWS L.

Module Type VALUE_DOMAIN_TIME (L : LANG_T) (Import D : VALUE_DOMAIN L).
  (* spec: size work gwork wsize *)
  Parameter size : t -> nat.
  Parameter work : L.op -> list t -> nat.
  Parameter gwork : L.guard -> list t -> nat.
  Parameter wsize : wparam -> nat.
  Definition wunits (_ : t) : nat := 0.
  Parameter T_leb T_join T_meet : t -> t -> N.
  Parameter T_is_bot : t -> N.
  Parameter T_widen : wparam -> t -> t -> N.
  Parameter T_narrow : t -> t -> N.
  Parameter T_forward : L.op -> list t -> N.
  Parameter T_backward : L.op -> t -> list t -> N.
  Parameter T_guard : L.guard -> list t -> N.
  Parameter c_val : N.
  Definition c_lat : N := c_val.
  (** The lattice constant pays for at least one call. *)
  Parameter c_lat_pos : (1 <= c_lat)%N.
  (** Inclusion testing costs at most the combined abstract sizes. *)
  Parameter T_leb_le : forall a b, (T_leb a b <= c_val * N.of_nat (size a + size b + 1))%N.
  (** Join costs at most the combined abstract sizes. *)
  Parameter T_join_le : forall a b, (T_join a b <= c_val * N.of_nat (size a + size b + 1))%N.
  (** Meet costs at most the combined abstract sizes. *)
  Parameter T_meet_le : forall a b, (T_meet a b <= c_val * N.of_nat (size a + size b + 1))%N.
  (** Bottom testing costs at most the abstract size. *)
  Parameter T_is_bot_le : forall a, (T_is_bot a <= c_val * N.of_nat (size a + 1))%N.
  (** Widening charges both values and the widening parameters. *)
  Parameter T_widen_le : forall p a b,
    (T_widen p a b <= c_val * N.of_nat (size a + size b + wsize p + 1))%N.
  (** Narrowing charges both abstract values. *)
  Parameter T_narrow_le : forall a b,
    (T_narrow a b <= c_val * N.of_nat (size a + size b + 1))%N.
  (** Forward transfer is bounded by operator work. *)
  Parameter T_forward_le : forall o xs, (T_forward o xs <= c_val * N.of_nat (work o xs + 1))%N.
  (** Backward transfer additionally charges the requested result. *)
  Parameter T_backward_le : forall o r xs,
    (T_backward o r xs <= c_val * N.of_nat (work o xs + size r + 1))%N.
  (** Guard transfer is bounded by guard work. *)
  Parameter T_guard_le : forall g xs, (T_guard g xs <= c_val * N.of_nat (gwork g xs + 1))%N.
  (** Forward results fit within the charged operator work. *)
  Parameter forward_size : forall o xs,
    (N.of_nat (size (forward o xs)) <= c_val * N.of_nat (work o xs + 1))%N.
  (** Meet results fit within the combined operand sizes. *)
  Parameter meet_size : forall a b,
    (N.of_nat (size (meet a b)) <= c_val * N.of_nat (size a + size b + 1))%N.
  (** Join results fit within the combined operand sizes. *)
  Parameter join_size : forall a b,
    (N.of_nat (size (join a b)) <= c_val * N.of_nat (size a + size b + 1))%N.
  (** Widening results fit within the operand and parameter sizes. *)
  Parameter widen_size : forall p a b,
    (N.of_nat (size (widen p a b)) <= c_val * N.of_nat (size a + size b + wsize p + 1))%N.
  (** Backward results fit within the charged work and request size. *)
  Parameter backward_size : forall o r xs,
    (N.of_nat (fold_right Nat.add 0%nat (map size (backward o r xs))) <=
      c_val * N.of_nat (work o xs + size r + 1))%N.
  (** Guard results fit within the charged guard work. *)
  Parameter guard_size : forall g xs,
    (N.of_nat (fold_right Nat.add 0%nat (map size (guard g xs))) <=
      c_val * N.of_nat (gwork g xs + 1))%N.
  (** Operator work accounts for every operand size. *)
  Parameter work_sizes : forall o xs, fold_right Nat.add 0%nat (map size xs) <= work o xs.
  (** Guard work accounts for every operand size. *)
  Parameter gwork_sizes : forall g xs, fold_right Nat.add 0%nat (map size xs) <= gwork g xs.
End VALUE_DOMAIN_TIME.

Module Type VALUE_DOMAIN_T (L : LANG_T) := VALUE_DOMAIN L <+ VALUE_DOMAIN_TIME L.

Module Type NUM_VIEW (L : LANG).
  (* spec: num *)
  Parameter num : L.val -> Z.
End NUM_VIEW.

(** Bounds admit finite endpoints and both infinities. *)
Inductive bnd : Type :=
  | NegInf
  | Fin (z : Z)
  | PosInf.

(** Membership uses inclusive finite endpoints and excludes reversed infinities. *)
Definition in_bnd (lo hi : bnd) (z : Z) : Prop :=
  (match lo with
   | NegInf => True
   | Fin l => (l <= z)%Z
   | PosInf => False
   end) /\
  (match hi with
   | NegInf => False
   | Fin h => (z <= h)%Z
   | PosInf => True
   end).

Module Type RANGE_QUERY (L : LANG) (N : NUM_VIEW L) (Import D : VALUE_DOMAIN L).
  Parameter range : t -> bnd * bnd.
  (** Every represented numeric value lies in the queried range. *)
  Parameter range_sound : forall a c,
    gamma a c -> in_bnd (fst (range a)) (snd (range a)) (N.num c).
End RANGE_QUERY.

Module Type RANGE_REFINE (L : LANG) (N : NUM_VIEW L) (Import D : VALUE_DOMAIN L).
  Parameter refine_range : bnd -> bnd -> t -> t.
  (** Range refinement retains values satisfying both constraints. *)
  Parameter refine_range_sound : forall lo hi a c,
    gamma a c -> in_bnd lo hi (N.num c) -> gamma (refine_range lo hi a) c.
  (** Range refinement descends in the abstract order. *)
  Parameter refine_range_lower : forall lo hi a, leb (refine_range lo hi a) a = true.
End RANGE_REFINE.

Create HintDb galois_gamma.
#[export] Hint Resolve Forall2_nil Forall2_cons : galois_gamma.

(** Semantic search uses registered transfer laws at a fixed depth.
    Clients register their domain's soundness lemmas in [galois_gamma]. *)
Ltac gamma_auto :=
  repeat match goal with
  | H : _ /\ _ |- _ => destruct H
  | |- _ /\ _ => split
  end;
  eauto 6 with galois_gamma.
