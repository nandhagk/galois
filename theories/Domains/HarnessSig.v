(** * Transfer harness interfaces

    The harness combines singleton evaluation with optional abstract transfer entries.
    For example, a missing forward entry falls back to top.
    Builds on: LangSig, ValueSig and LatticeSig. *)

From Stdlib Require Import List NArith.
From Argent Require Import BigO.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.

Module Type HARNESS_BASE_OPS (L : LANG_OPS).
  Include ALATTICE_OPS.
  Parameter point : t -> option L.val.
  Parameter abst : L.val -> t.
End HARNESS_BASE_OPS.

Module Type HARNESS_BASE_LAWS (L : LANG) (Import B : HARNESS_BASE_OPS L).
  (* spec: gamma *)
  Parameter gamma : t -> L.val -> Prop.
  (** Inclusion retains every represented value. *)
  Parameter gamma_mono : forall a b c, leb a b = true -> gamma a c -> gamma b c.
  (** Bottom represents no value. *)
  Parameter gamma_bot : forall c, ~ gamma bot c.
  (** Top represents every value. *)
  Parameter gamma_top : forall c, gamma top c.
  (** Meet retains values common to both inputs. *)
  Parameter gamma_meet : forall a b c, gamma a c -> gamma b c -> gamma (meet a b) c.
  (** Recognized bottoms represent no value. *)
  Parameter is_bot_sound : forall a c, is_bot a = true -> ~ gamma a c.
  (** Every value below a recognized bottom is recognized as bottom. *)
  Parameter is_bot_below : forall a b, leb a b = true -> is_bot b = true -> is_bot a = true.
  (** A recognized singleton identifies every represented value. *)
  Parameter point_sound : forall a v c, point a = Some v -> gamma a c -> c = v.
  (** Abstraction retains its concrete argument. *)
  Parameter abst_sound : forall v, gamma (abst v) v.
End HARNESS_BASE_LAWS.

Module Type HARNESS_BASE (L : LANG) :=
  HARNESS_BASE_OPS L <+ LATTICE_LAWS <+ HAS_TOP_LAWS <+ HAS_MEET_LAWS <+
  WIDENING_LAWS <+ HARNESS_BASE_LAWS L.

Module Type HARNESS_BASE_TIME (L : LANG_T) (Import B : HARNESS_BASE L).
  (* spec: bsize wsize *)
  Parameter bsize : t -> nat.
  Parameter wsize : wparam -> nat.
  Parameter T_leb T_join T_meet T_narrow : t -> t -> N.
  Parameter T_is_bot T_point : t -> N.
  Parameter T_abst : L.val -> N.
  Parameter T_widen : wparam -> t -> t -> N.
  Parameter c_base : N.
  (** Inclusion charges the input sizes. *)
  Parameter T_leb_le : forall a b, (T_leb a b <= c_base * N.of_nat ((bsize a + bsize b + 1)%nat))%N.
  (** Join charges the input sizes. *)
  Parameter T_join_le : forall a b, (T_join a b <= c_base * N.of_nat ((bsize a + bsize b +
    1)%nat))%N.
  (** Meet charges the input sizes. *)
  Parameter T_meet_le : forall a b, (T_meet a b <= c_base * N.of_nat ((bsize a + bsize b +
    1)%nat))%N.
  (** Narrowing charges the input sizes. *)
  Parameter T_narrow_le : forall a b, (T_narrow a b <= c_base * N.of_nat ((bsize a + bsize b +
    1)%nat))%N.
  (** Bottom recognition charges its input size. *)
  Parameter T_is_bot_le : forall a, (T_is_bot a <= c_base * N.of_nat ((bsize a + 1)%nat))%N.
  (** Singleton recognition charges its input size. *)
  Parameter T_point_le : forall a, (T_point a <= c_base * N.of_nat ((bsize a + 1)%nat))%N.
  (** Widening charges its parameters and both input sizes. *)
  Parameter T_widen_le : forall p a b,
    (T_widen p a b <= c_base * N.of_nat ((bsize a + bsize b + wsize p + 1)%nat))%N.
  (** Meet results fit within the charged operand sizes. *)
  Parameter meet_size_le : forall a b,
    (N.of_nat (bsize (meet a b)) <= c_base * N.of_nat (bsize a + bsize b + 1))%N.
  (** Join results fit within the charged operand sizes. *)
  Parameter join_size_le : forall a b,
    (N.of_nat (bsize (join a b)) <= c_base * N.of_nat (bsize a + bsize b + 1))%N.
  (** Widening results fit within the operand and parameter sizes. *)
  Parameter widen_size_le : forall p a b,
    (N.of_nat (bsize (widen p a b)) <= c_base * N.of_nat (bsize a + bsize b + wsize p + 1))%N.
  (** Abstraction results fit within their abstraction time. *)
  Parameter abst_size_le : forall v,
    (N.of_nat (bsize (abst v)) <= c_base * (T_abst v + 1))%N.
End HARNESS_BASE_TIME.

Module Type HARNESS_BASE_T (L : LANG_T) := HARNESS_BASE L <+ HARNESS_BASE_TIME L.

Module Type TABLE_OPS (L : LANG_OPS) (B : HARNESS_BASE_OPS L).
  Parameter fwd : L.op -> list B.t -> option B.t.
  Parameter bwd : L.op -> B.t -> list B.t -> option (list B.t).
  Parameter grd : L.guard -> list B.t -> option (list B.t).
End TABLE_OPS.

Module Type TABLE_LAWS (L : LANG) (B : HARNESS_BASE L) (Import T : TABLE_OPS L B).
  (** A modeled forward entry retains concrete results. *)
  Parameter fwd_sound : forall o xs cs c r, fwd o xs = Some r ->
    Forall2 B.gamma xs cs -> L.eval o cs = Some c -> B.gamma r c.
  (** A modeled backward entry retains consistent operands. *)
  Parameter bwd_sound : forall o r xs ys cs c, bwd o r xs = Some ys ->
    Forall2 B.gamma xs cs -> L.eval o cs = Some c -> B.gamma r c -> Forall2 B.gamma ys cs.
  (** A modeled guard entry retains satisfying operands. *)
  Parameter grd_sound : forall g xs ys cs, grd g xs = Some ys ->
    Forall2 B.gamma xs cs -> L.holds g cs -> Forall2 B.gamma ys cs.
End TABLE_LAWS.

Module Type TABLE (L : LANG) (B : HARNESS_BASE L) := TABLE_OPS L B <+ TABLE_LAWS L B.

Module Type TABLE_TIME (L : LANG_T) (B : HARNESS_BASE_T L) (Import T : TABLE L B).
  (* spec: twork tgwork *)
  Parameter twork : L.op -> list B.t -> nat.
  Parameter tgwork : L.guard -> list B.t -> nat.
  Parameter T_fwd : L.op -> list B.t -> N.
  Parameter T_bwd : L.op -> B.t -> list B.t -> N.
  Parameter T_grd : L.guard -> list B.t -> N.
  Parameter c_tab : N.
  (** Forward entries charge their table work. *)
  Parameter T_fwd_le : forall o xs, (T_fwd o xs <= c_tab * N.of_nat ((twork o xs + 1)%nat))%N.
  (** Backward entries additionally charge the requested result. *)
  Parameter T_bwd_le : forall o r xs,
    (T_bwd o r xs <= c_tab * N.of_nat ((twork o xs + B.bsize r + 1)%nat))%N.
  (** Guard entries charge their table work. *)
  Parameter T_grd_le : forall g xs, (T_grd g xs <= c_tab * N.of_nat ((tgwork g xs + 1)%nat))%N.
  (** Abstracting an evaluated singleton is charged to the same table work. *)
  Parameter T_abst_le : forall v xs o cs, L.eval o cs = Some v ->
    Forall2 (fun x c => B.point x = Some c) xs cs ->
    (B.T_abst v <= c_tab * N.of_nat ((twork o xs + 1)%nat))%N.
  (** Forward table results fit within the charged table work. *)
  Parameter fwd_size_le : forall o xs r, fwd o xs = Some r ->
    (N.of_nat (B.bsize r) <= c_tab * N.of_nat (twork o xs + 1))%N.
  (** Backward table results charge their payload sizes and list length. *)
  Parameter bwd_size_le : forall o r xs ys, bwd o r xs = Some ys ->
    (N.of_nat (fold_right Nat.add 0%nat (map B.bsize ys) + length ys) <=
      c_tab * N.of_nat (twork o xs + B.bsize r + 1))%N.
  (** Guard table results charge their payload sizes and list length. *)
  Parameter grd_size_le : forall g xs ys, grd g xs = Some ys ->
    (N.of_nat (fold_right Nat.add 0%nat (map B.bsize ys) + length ys) <=
      c_tab * N.of_nat (tgwork g xs + 1))%N.
End TABLE_TIME.

Module Type TABLE_T (L : LANG_T) (B : HARNESS_BASE_T L) :=
  TABLE L B <+ TABLE_TIME L B.

Module Type HARNESS_OPS (L : LANG_OPS) (B : HARNESS_BASE_OPS L) (T : TABLE_OPS L B).
  Include VALUE_DOMAIN_OPS L with Definition t := B.t with Definition wparam := B.wparam.
  Parameter points : list B.t -> option (list L.val).
  Parameter meet_all : list B.t -> list B.t -> list B.t.
End HARNESS_OPS.

Module Type HARNESS (L : LANG) (B : HARNESS_BASE L) (T : TABLE L B) :=
  HARNESS_OPS L B T <+ LATTICE_LAWS <+ HAS_TOP_LAWS <+ HAS_MEET_LAWS <+
  WIDENING_LAWS <+ VALUE_DOMAIN_LAWS L.

Module Type HARNESS_TIME (L : LANG_T) (B : HARNESS_BASE_T L) (T : TABLE_T L B)
    (Import H : HARNESS L B T).
  Include VALUE_DOMAIN_TIME L H.
  Parameter T_points : list B.t -> N.
  Parameter T_meet_all : list B.t -> list B.t -> N.
  Parameter c_harness : N.
  (** Singleton collection charges a linear scan of all operands. *)
  Parameter T_points_le : forall xs,
    (T_points xs <= c_harness *
      N.of_nat ((fold_right Nat.add 0%nat (map B.bsize xs) + length xs + 1)%nat))%N.
  (** Positional meet charges both lists. *)
  Parameter T_meet_all_le : forall xs ys,
    (T_meet_all xs ys <= c_harness *
      N.of_nat ((fold_right Nat.add 0%nat (map B.bsize xs) +
        fold_right Nat.add 0%nat (map B.bsize ys) + length xs + length ys + 1)%nat))%N.
End HARNESS_TIME.

Module Type HARNESS_T (L : LANG_T) (B : HARNESS_BASE_T L) (T : TABLE_T L B) :=
  HARNESS L B T <+ HARNESS_TIME L B T.

Module Type HARNESS_PLAN (L : LANG_T) (B : HARNESS_BASE_T L) (T : TABLE_T L B)
    (Import H : HARNESS_T L B T).
  Definition opt_vals (xs : list B.t) : list L.val :=
    match points xs with Some cs => cs | None => nil end.
  Parameter k_points k_meet k_forward k_backward k_guard : N.
  (** Harness concretization uses the base interpretation. *)
  Parameter F0_gamma : forall a c, gamma a c <-> B.gamma a c.
  (** Harness inclusion uses the base order. *)
  Parameter F0_leb : forall a b, leb a b = B.leb a b.
  (** Harness join uses the base join. *)
  Parameter F0_join : forall a b, join a b = B.join a b.
  (** Harness meet uses the base meet. *)
  Parameter F0_meet : forall a b, meet a b = B.meet a b.
  (** Harness sizes use the base sizes. *)
  Parameter F0_size : forall a, size a = B.bsize a.
  (** Harness forward work charges operands, concrete evaluation and the table. *)
  Parameter F0_work : forall o xs, work o xs =
    fold_right Nat.add 0%nat (map B.bsize xs) + length xs +
    L.work o (opt_vals xs) + T.twork o xs.
  (** Harness guard work charges operands and the table. *)
  Parameter F0_gwork : forall g xs, gwork g xs =
    fold_right Nat.add 0%nat (map B.bsize xs) + length xs + T.tgwork g xs.
  (** Collected singletons agree with every represented concrete list. *)
  Parameter F1_points_sound : forall xs cs vs,
    Forall2 B.gamma xs cs -> points xs = Some vs -> vs = cs.
  (** Represented concrete lists contain no recognized bottom. *)
  Parameter F2_no_bot : forall xs cs,
    Forall2 B.gamma xs cs -> existsb B.is_bot xs = false.
  (** Equal-length positional meets retain common concrete operands. *)
  Parameter F3_meet_all_sound : forall xs ys cs, length ys = length xs ->
    Forall2 B.gamma xs cs -> Forall2 B.gamma ys cs -> Forall2 B.gamma (meet_all xs ys) cs.
  (** Positional meet descends in every original operand. *)
  Parameter F4_meet_all_refines : forall xs ys,
    Forall2 (fun y x => B.leb y x = true) (meet_all xs ys) xs.
  (** Singleton collection charges one recognition per operand. *)
  Parameter T1_points : forall xs, (T_points xs <=
    k_points * (fold_right N.add 0 (map (fun x => B.T_point x + 1) xs) + 1))%N.
  (** Forward transfer charges collection, concrete evaluation and the table. *)
  Parameter T2_forward : forall o xs,
    (T_forward o xs <= k_forward *
      N.of_nat ((fold_right Nat.add 0%nat (map B.bsize xs) + length xs +
        L.work o (opt_vals xs) + T.twork o xs + 1)%nat))%N.
  (** Backward transfer charges the table, lengths and positional meets. *)
  Parameter T3_backward : forall o r xs, (T_backward o r xs <= k_backward *
    (T.T_bwd o r xs + N.of_nat ((length xs)%nat) +
     match T.bwd o r xs with
     | Some ys => N.of_nat ((length ys)%nat) + T_meet_all xs ys
     | None => 0
     end + 1))%N.
  (** Guard transfer charges the table, lengths and positional meets. *)
  Parameter T4_guard : forall g xs, (T_guard g xs <= k_guard *
    (T.T_grd g xs + N.of_nat ((length xs)%nat) +
     match T.grd g xs with
     | Some ys => N.of_nat ((length ys)%nat) + T_meet_all xs ys
     | None => 0
     end + 1))%N.
End HARNESS_PLAN.

Module Type HARNESS_ALL (L : LANG_T) (B : HARNESS_BASE_T L) (T : TABLE_T L B) :=
  HARNESS_T L B T <+ HARNESS_PLAN L B T.
