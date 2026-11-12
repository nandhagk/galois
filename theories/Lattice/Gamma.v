(** * Concretization signatures

    Concretization relates abstract values to concrete values and respects the order.
    For example, the bottom extension requires a recognized bottom to contain no concrete value.
    Builds on: Base.KeySig and Lattice.LatticeSig. *)

From Galois.Base Require Import KeySig.
From Galois.Lattice Require Import LatticeSig.

Module Type GAMMA (C : TYPE) (L : LATTICE_OPS).
  (* spec: gamma *)
  Parameter gamma : L.t -> C.t -> Prop.
  (** Increasing an abstract value keeps every concrete value it contains. *)
  Parameter gamma_mono : forall a b c, L.leb a b = true -> gamma a c -> gamma b c.
End GAMMA.

Module Type GAMMA_BOT (C : TYPE) (L : LATTICE_OPS) (Import G : GAMMA C L).
  (** A recognized bottom contains no concrete value. *)
  Parameter gamma_bot : forall a c, L.is_bot a = true -> ~ gamma a c.
End GAMMA_BOT.

Module Type GAMMA_TOP (C : TYPE) (L : LATTICE_OPS) (T : HAS_TOP_OPS L)
    (Import G : GAMMA C L).
  (** Top contains every concrete value. *)
  Parameter gamma_top : forall c, gamma T.top c.
End GAMMA_TOP.

Module Type GAMMA_MEET (C : TYPE) (L : LATTICE_OPS) (M : HAS_MEET_OPS L)
    (Import G : GAMMA C L).
  (** Meet contains every concrete value shared by its operands. *)
  Parameter gamma_meet : forall a b c, gamma a c -> gamma b c -> gamma (M.meet a b) c.
End GAMMA_MEET.

Module Type REDUCER_SOUND (C : TYPE) (A B : LATTICE_OPS) (R : REDUCER_OPS A B)
    (GA : GAMMA C A) (GB : GAMMA C B).
  (** Reduction keeps every concrete value shared by both components. *)
  Parameter reduce_sound : forall a b c, GA.gamma a c -> GB.gamma b c ->
    GA.gamma (fst (R.reduce (a, b))) c /\ GB.gamma (snd (R.reduce (a, b))) c.
End REDUCER_SOUND.
