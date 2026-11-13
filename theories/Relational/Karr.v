(** * Linear equality states

    Integer elimination tracks the input multipliers used by every produced row.
    For example, eliminating x from x + y = 2 and x = 1 gives y = 1.
    Builds on: KarrSig and the binary trie code. *)
From Stdlib Require Import List ZArith NArith QArith Qfield Bool Lia Ring Psatz Permutation.
From Argent Require Import Time Std.
From Galois.Base Require Import KeySig Trie.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import EnvSig.
From Galois.Relational Require Import LinForm LinearizeSig NumStateSig LinCertSig KarrSig.
Import List.ListNotations.
Local Open Scope nat_scope.

Module List.
  TimeFun tl.
  TimeFun flat_map.
End List.

Module ListDef.
  TimeFun repeat.
  TimeFun firstn.
  TimeFun skipn.
End ListDef.

Fixpoint karr_list_eqb {A} (eqb : A -> A -> bool) (xs ys : list A) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs, y :: ys => eqb x y && karr_list_eqb eqb xs ys
  | _, _ => false
  end.

TimeFun karr_list_eqb.

(** A row carries its dense coordinates and its integer combination of the input rows. *)
Record karr_row := KRow {
  kcoeff : list Z;
  kright : Z;
  kweight : list Z;
  kscale : Z
}.

TimeFun kcoeff.
TimeFun kright.
TimeFun kweight.
TimeFun kscale.

(** Trie traversal returns stored values without constructing their positive keys. *)
Fixpoint karr_values_ne {A} (tr : trie_ne A) (acc : list A) : list A :=
  match tr with
  | N001 r => karr_values_ne r acc
  | N010 a => a :: acc
  | N011 a r => a :: karr_values_ne r acc
  | N100 l => karr_values_ne l acc
  | N101 l r => karr_values_ne l (karr_values_ne r acc)
  | N110 l a => karr_values_ne l (a :: acc)
  | N111 l a r => karr_values_ne l (a :: karr_values_ne r acc)
  end.

TimeFun karr_values_ne.

Definition karr_values {A} (tr : ptrie A) : list A :=
  match tr with
  | Empty => []
  | Nodes n => karr_values_ne n []
  end.

TimeFun karr_values.

(** Cross multiplication eliminates one coordinate without dividing. *)
Fixpoint karr_cross (a b : Z) (xs ys : list Z) : list Z :=
  match xs, ys with
  | x :: xs, y :: ys => (a * x - b * y)%Z :: karr_cross a b xs ys
  | _, _ => []
  end.

TimeFun karr_cross.

(** A quotient is used only when its remainder vanishes. *)
Definition karr_divisible (d z : Z) : bool := Z.eqb (z mod d) 0.

TimeFun karr_divisible.

(** All tracked coordinates must share a nonzero exact divisor. *)
Definition karr_exact (d : Z) (r : karr_row) : bool :=
  negb (Z.eqb d 0) &&
    (forallb (karr_divisible d) (kcoeff r) &&
      (karr_divisible d (kright r) &&
        (forallb (karr_divisible d) (kweight r) && karr_divisible d (kscale r)))).

TimeFun karr_exact.

Definition karr_quotient (d : Z) (r : karr_row) : karr_row :=
  KRow (map (fun z => (z / d)%Z) (kcoeff r)) ((kright r / d)%Z)
    (map (fun z => (z / d)%Z) (kweight r)) ((kscale r / d)%Z).

TimeFun karr_quotient.

(** Failed exactness keeps the integer cross product and its valid provenance. *)
Definition karr_divide (d : Z) (r : karr_row) : karr_row :=
  if karr_exact d r then karr_quotient d r else r.

TimeFun karr_divide.

(** Multiplication recovers each coordinate of an exactly divided row. *)
Definition karr_multiple (d : Z) (r s : karr_row) : Prop :=
  map (fun z => (d * z)%Z) (kcoeff r) = kcoeff s /\
  (d * kright r = kright s)%Z /\
  map (fun z => (d * z)%Z) (kweight r) = kweight s /\
  (d * kscale r = kscale s)%Z.

(** A checked zero remainder identifies an exact integer quotient. *)
Lemma karr_divisible_exact : forall d z, d <> 0%Z -> karr_divisible d z = true ->
  (d * (z / d) = z)%Z.
Proof.
  intros d z Hnonzero Hexact. unfold karr_divisible in Hexact.
  apply Z.eqb_eq in Hexact. pose proof (Z.div_mod z d Hnonzero). nia.
Qed.

(** Exact division followed by multiplication restores a whole coefficient list. *)
Lemma karr_exact_list : forall d zs, d <> 0%Z ->
  forallb (karr_divisible d) zs = true ->
  map (fun z => (d * z)%Z) (map (fun z => (z / d)%Z) zs) = zs.
Proof.
  intros d zs Hnonzero Hchecked. rewrite map_map.
  transitivity (map (fun z : Z => z) zs); [|apply map_id].
  apply map_ext_in. intros z Hin. apply karr_divisible_exact; [exact Hnonzero|].
  exact (proj1 (forallb_forall _ _) Hchecked z Hin).
Qed.

(** Either branch returns a row related to its input by a nonzero integer factor. *)
Lemma karr_divide_factor : forall d r,
  exists factor, factor <> 0%Z /\ karr_multiple factor (karr_divide d r) r.
Proof.
  intros d r. unfold karr_divide. destruct (karr_exact d r) eqn:Hchecked.
  - unfold karr_exact in Hchecked.
    apply andb_true_iff in Hchecked as [Hnonzero Hchecked].
    apply negb_true_iff, Z.eqb_neq in Hnonzero.
    apply andb_true_iff in Hchecked as [Hcoeff Hchecked].
    apply andb_true_iff in Hchecked as [Hright Hchecked].
    apply andb_true_iff in Hchecked as [Hweight Hscale].
    exists d. split; [exact Hnonzero|].
    unfold karr_multiple, karr_quotient; cbn [kcoeff kright kweight kscale].
    repeat split; first [now apply karr_exact_list|now apply karr_divisible_exact].
  - exists 1%Z. split; [lia|]. unfold karr_multiple.
    assert (Hone : forall zs : list Z, map (fun z => (1 * z)%Z) zs = zs).
    { intro zs. induction zs as [|z zs IH]; cbn [map]; [reflexivity|].
      f_equal; [ring|exact IH]. }
    repeat split; try ring; apply Hone.
Qed.

Definition karr_head (r : karr_row) : Z :=
  match kcoeff r with [] => 0%Z | z :: _ => z end.

TimeFun karr_head.

Definition karr_tail (r : karr_row) : karr_row :=
  KRow (tl (kcoeff r)) (kright r) (kweight r) (kscale r).

TimeFun karr_tail.

Definition karr_restore (r : karr_row) : karr_row :=
  KRow (0%Z :: kcoeff r) (kright r) (kweight r) (kscale r).

TimeFun karr_restore.

Definition karr_reduce (d a b : Z) (p r : karr_row) : karr_row :=
  karr_divide d
    (KRow (karr_cross a b (kcoeff r) (kcoeff p))
      (a * kright r - b * kright p)%Z
      (karr_cross a b (kweight r) (kweight p))
      (a * kscale r - b * kscale p)%Z).

TimeFun karr_reduce.

(** A finite rational store evaluates the dense coefficient coordinates in order. *)
Fixpoint karr_eval (qs : list Q) (zs : list Z) : Q :=
  match qs, zs with
  | q :: qs, z :: zs => (inject_Z z * q + karr_eval qs zs)%Q
  | _, _ => 0%Q
  end.

(** Dense row semantics is an equality over a finite rational store. *)
Definition karr_models (qs : list Q) (r : karr_row) : Prop :=
  (karr_eval qs (kcoeff r) == inject_Z (kright r))%Q.

Fixpoint karr_pivot (rs : list karr_row) : option (karr_row * list karr_row) :=
  match rs with
  | [] => None
  | r :: rs =>
    if Z.eqb (karr_head r) 0 then
      match karr_pivot rs with
      | None => None
      | Some (p, rest) => Some (p, r :: rest)
      end
    else Some (r, rs)
  end.

TimeFun karr_pivot.

(** Elimination visits each coefficient column once and retains the row certificates. *)
Fixpoint karr_bareiss (cols : nat) (previous : Z) (rs : list karr_row)
    : list karr_row :=
  match cols with
  | 0 => rs
  | S cols =>
    match karr_pivot rs with
    | None => map karr_restore (karr_bareiss cols previous (map karr_tail rs))
    | Some (p, rest) =>
      let a := karr_head p in
      let rest' := map (fun r =>
        karr_tail (karr_reduce previous a (karr_head r) p r)) rest in
      p :: map karr_restore (karr_bareiss cols a rest')
    end
  end.

TimeFun karr_bareiss.

Fixpoint karr_first (xs : list Z) : option (nat * Z) :=
  match xs with
  | [] => None
  | x :: xs =>
    if Z.eqb x 0 then
      match karr_first xs with
      | None => None
      | Some (i, a) => Some (S i, a)
      end
    else Some (0, x)
  end.

TimeFun karr_first.

Fixpoint karr_nth (i : nat) (xs : list Z) : Z :=
  match i, xs with
  | 0, x :: _ => x
  | S i, _ :: xs => karr_nth i xs
  | _, _ => 0%Z
  end.

TimeFun karr_nth.

(** A target follows the same pivot operations as an appended matrix row. *)
Fixpoint karr_target (rs : list karr_row) (previous : Z) (r : karr_row) : karr_row :=
  match rs with
  | [] => r
  | p :: rs =>
    match karr_first (kcoeff p) with
    | None => karr_target rs previous r
    | Some (i, a) =>
      karr_target rs a (karr_reduce previous a (karr_nth i (kcoeff r)) p r)
    end
  end.

TimeFun karr_target.

Fixpoint karr_unit (length index : nat) : list Z :=
  match length with
  | 0 => []
  | S length =>
    match index with
    | 0 => 1%Z :: repeat 0%Z length
    | S index => 0%Z :: karr_unit length index
    end
  end.

TimeFun karr_unit.

Definition karr_zero (r : karr_row) : bool := forallb (Z.eqb 0) (kcoeff r).

TimeFun karr_zero.

(** A selected pivot is nonzero and only changes the ordering of the rows. *)
Lemma karr_pivot_some : forall rs p rest, karr_pivot rs = Some (p, rest) ->
  karr_head p <> 0%Z /\ Permutation rs (p :: rest).
Proof.
  induction rs as [|r rs IH]; intros p rest Hpivot; cbn [karr_pivot] in Hpivot;
    [discriminate|].
  destruct (Z.eqb (karr_head r) 0) eqn:Hhead.
  - destruct (karr_pivot rs) as [[q tail]|] eqn:Hnext; [|discriminate].
    inversion Hpivot; subst p rest. destruct (IH q tail eq_refl) as [Hnonzero Hperm].
    split; [exact Hnonzero|]. eapply Permutation_trans.
    + apply perm_skip. exact Hperm.
    + apply perm_swap.
  - inversion Hpivot; subst p rest. split; [now apply Z.eqb_neq|apply Permutation_refl].
Qed.

(** Failing to find a pivot means every leading coefficient vanishes. *)
Lemma karr_pivot_none : forall rs, karr_pivot rs = None ->
  Forall (fun r => karr_head r = 0%Z) rs.
Proof.
  induction rs as [|r rs IH]; intro Hnone; [constructor|].
  cbn [karr_pivot] in Hnone. destruct (Z.eqb (karr_head r) 0) eqn:Hhead;
    [|discriminate].
  destruct (karr_pivot rs) as [[p rest]|] eqn:Hnext; [discriminate|].
  constructor; [now apply Z.eqb_eq|now apply IH].
Qed.

(** Every reported first coefficient is nonzero. *)
Lemma karr_first_nonzero : forall zs i a, karr_first zs = Some (i, a) -> a <> 0%Z.
Proof.
  induction zs as [|z zs IH]; intros i a Hfirst; cbn [karr_first] in Hfirst;
    [discriminate|].
  destruct (Z.eqb z 0) eqn:Hzero.
  - destruct (karr_first zs) as [[j b]|] eqn:Hnext; [|discriminate].
    inversion Hfirst; subst i a. now apply (IH j b).
  - inversion Hfirst; subst i a. now apply Z.eqb_neq.
Qed.

(** Exact division preserves the number of dense coordinates. *)
Lemma karr_divide_width : forall d r,
  length (kcoeff (karr_divide d r)) = length (kcoeff r).
Proof.
  intros d r. unfold karr_divide. destruct (karr_exact d r); [|reflexivity].
  unfold karr_quotient. cbn [kcoeff]. apply length_map.
Qed.

(** Crossing equally wide rows retains their width. *)
Lemma karr_cross_width : forall a b xs ys, length xs = length ys ->
  length (karr_cross a b xs ys) = length xs.
Proof.
  intros a b xs. induction xs as [|x xs IH]; intros [|y ys] Hwidth;
    cbn [length karr_cross] in *; try discriminate; [reflexivity|].
  f_equal. apply IH. now injection Hwidth.
Qed.

(** Reduction retains the width shared by its input rows. *)
Lemma karr_reduce_width : forall d a b p r,
  length (kcoeff r) = length (kcoeff p) ->
  length (kcoeff (karr_reduce d a b p r)) = length (kcoeff r).
Proof.
  intros d a b p r Hwidth. unfold karr_reduce. rewrite karr_divide_width.
  cbn [kcoeff]. now apply karr_cross_width.
Qed.

(** Dropping a leading coordinate reduces a positive width by one. *)
Lemma karr_tail_width : forall n r, length (kcoeff r) = S n ->
  length (kcoeff (karr_tail r)) = n.
Proof.
  intros n [zs rhs ws sc] Hwidth; cbn [kcoeff karr_tail] in *.
  destruct zs; cbn [length tl] in *; lia.
Qed.

(** Restoring a zero coordinate increases the width by one. *)
Lemma karr_restore_width : forall r,
  length (kcoeff (karr_restore r)) = S (length (kcoeff r)).
Proof.
  reflexivity.
Qed.

(** The recursion's shape records strictly advancing pivot positions. *)
Inductive karr_echelon : nat -> list karr_row -> Prop :=
  | karr_echelon_zero : forall rs,
      Forall (fun r => kcoeff r = []) rs -> karr_echelon 0 rs
  | karr_echelon_skip : forall n rs,
      karr_echelon n rs -> karr_echelon (S n) (map karr_restore rs)
  | karr_echelon_pivot : forall n p rs,
      length (kcoeff p) = S n -> karr_head p <> 0%Z ->
      karr_echelon n rs -> karr_echelon (S n) (p :: map karr_restore rs).

(** Eliminating every coordinate produces a triangular basis. *)
Lemma karr_bareiss_echelon : forall n d rs,
  Forall (fun r => length (kcoeff r) = n) rs ->
  karr_echelon n (karr_bareiss n d rs).
Proof.
  intro n. induction n as [|n IH]; intros d rs Hwidth; cbn [karr_bareiss].
  - apply karr_echelon_zero. apply Forall_forall. intros r Hin.
    pose proof (proj1 (Forall_forall _ _) Hwidth r Hin) as Hr.
    now apply length_zero_iff_nil in Hr.
  - destruct (karr_pivot rs) as [[p rest]|] eqn:Hpivot.
    + destruct (karr_pivot_some rs p rest Hpivot) as [Hhead Hperm].
      assert (Hordered : Forall (fun r => length (kcoeff r) = S n) (p :: rest)).
      { eapply Permutation_Forall; [exact Hperm|exact Hwidth]. }
      inversion Hordered as [|p' rest' Hp Hrest]; subst p' rest'.
      apply karr_echelon_pivot; [exact Hp|exact Hhead|].
      apply IH. apply Forall_forall. intros r Hin.
      apply in_map_iff in Hin as [s [Heq Hin]]. subst r.
      apply karr_tail_width. rewrite karr_reduce_width.
      * exact (proj1 (Forall_forall _ _) Hrest s Hin).
      * rewrite Hp. exact (proj1 (Forall_forall _ _) Hrest s Hin).
    + apply karr_echelon_skip. apply IH. apply Forall_forall. intros r Hin.
      apply in_map_iff in Hin as [s [Heq Hin]]. subst r.
      apply karr_tail_width. exact (proj1 (Forall_forall _ _) Hwidth s Hin).
Qed.
(** Division preserves a vanishing leading coordinate in either checked branch. *)
Lemma karr_divide_head_zero : forall d r, karr_head r = 0%Z ->
  karr_head (karr_divide d r) = 0%Z.
Proof.
  intros d r Hzero. unfold karr_divide. destruct (karr_exact d r); [|exact Hzero].
  unfold karr_head, karr_quotient in *. cbn [kcoeff].
  destruct (kcoeff r) as [|z zs]; cbn [map] in *; [reflexivity|].
  subst z. reflexivity.
Qed.

(** Crossing at the two leading coefficients eliminates that coordinate exactly. *)
Lemma karr_reduce_head_zero : forall d p r,
  karr_head (karr_reduce d (karr_head p) (karr_head r) p r) = 0%Z.
Proof.
  intros d [ps pr pw pc] [rs rr rw rc]. unfold karr_reduce.
  apply karr_divide_head_zero. destruct ps as [|p ps], rs as [|r rs];
    cbn [kcoeff karr_cross karr_head]; try reflexivity. ring.
Qed.

(** A reported first coefficient is found at its reported index. *)
Lemma karr_first_nth : forall zs i a, karr_first zs = Some (i, a) ->
  karr_nth i zs = a.
Proof.
  induction zs as [|z zs IH]; intros i a Hfirst; cbn [karr_first] in Hfirst;
    [discriminate|].
  destruct (Z.eqb z 0) eqn:Hzero.
  - destruct (karr_first zs) as [[j b]|] eqn:Hnext; [|discriminate].
    inversion Hfirst; subst i a. cbn [karr_nth]. now apply (IH j b).
  - inversion Hfirst; reflexivity.
Qed.




(** Integer nonzero factors remain nonzero in the rational field. *)
Lemma karr_inject_nonzero : forall z, z <> 0%Z -> ~ (inject_Z z == 0)%Q.
Proof.
  intros z Hnonzero Hzero. apply Hnonzero.
  apply (proj1 (inject_Z_injective z 0)). exact Hzero.
Qed.

(** Dense evaluation distributes over coefficient scaling. *)
Lemma karr_eval_scale : forall qs d zs,
  (karr_eval qs (map (fun z => (d * z)%Z) zs) ==
    inject_Z d * karr_eval qs zs)%Q.
Proof.
  intro qs. induction qs as [|q qs IH]; intros d [|z zs];
    cbn [map karr_eval]; try ring.
  rewrite inject_Z_mult. setoid_rewrite (IH d zs). ring.
Qed.

(** Dense evaluation distributes over equally wide cross products. *)
Lemma karr_eval_cross : forall qs a b xs ys, length xs = length ys ->
  (karr_eval qs (karr_cross a b xs ys) ==
    inject_Z a * karr_eval qs xs - inject_Z b * karr_eval qs ys)%Q.
Proof.
  intro qs. induction qs as [|q qs IH]; intros a b [|x xs] [|y ys] Hwidth;
    cbn [length] in Hwidth; try discriminate; cbn [karr_eval karr_cross]; try ring.
  unfold Z.sub. rewrite inject_Z_plus, inject_Z_opp, !inject_Z_mult.
  setoid_rewrite (IH a b xs ys ltac:(lia)). ring.
Qed.

(** A tracked integer factor scales the whole rational equality defect. *)
Lemma karr_multiple_eval : forall factor r s qs, karr_multiple factor r s ->
  (inject_Z factor * (karr_eval qs (kcoeff r) - inject_Z (kright r)) ==
    karr_eval qs (kcoeff s) - inject_Z (kright s))%Q.
Proof.
  intros factor r s qs [Hcoeff [Hright _]]. rewrite <- Hcoeff, <- Hright.
  setoid_rewrite karr_eval_scale. rewrite inject_Z_mult. ring.
Qed.

(** Each reduction has a nonzero factor relating its defect to the two input defects. *)
Lemma karr_reduce_eval : forall qs d a b p r,
  length (kcoeff r) = length (kcoeff p) ->
  exists factor, factor <> 0%Z /\
    (inject_Z factor *
      (karr_eval qs (kcoeff (karr_reduce d a b p r)) -
        inject_Z (kright (karr_reduce d a b p r))) ==
      inject_Z a * (karr_eval qs (kcoeff r) - inject_Z (kright r)) -
      inject_Z b * (karr_eval qs (kcoeff p) - inject_Z (kright p)))%Q.
Proof.
  intros qs d a b p r Hwidth. unfold karr_reduce.
  set (raw := KRow (karr_cross a b (kcoeff r) (kcoeff p))
    (a * kright r - b * kright p)%Z
    (karr_cross a b (kweight r) (kweight p)) (a * kscale r - b * kscale p)%Z).
  destruct (karr_divide_factor d raw) as [factor [Hnonzero Hmultiple]].
  exists factor. split; [exact Hnonzero|].
  eapply Qeq_trans; [exact (karr_multiple_eval factor _ _ qs Hmultiple)|].
  unfold raw. cbn [kcoeff kright].
  setoid_rewrite (karr_eval_cross qs a b _ _ Hwidth).
  unfold Z.sub. rewrite inject_Z_plus, inject_Z_opp, !inject_Z_mult. ring.
Qed.

(** Retaining a satisfied nonzero pivot makes reduction equivalent to the original row. *)
Lemma karr_reduce_models : forall qs d a b p r,
  length (kcoeff r) = length (kcoeff p) -> a <> 0%Z -> karr_models qs p ->
  (karr_models qs (karr_reduce d a b p r) <-> karr_models qs r).
Proof.
  intros qs d a b p r Hwidth Ha Hp.
  destruct (karr_reduce_eval qs d a b p r Hwidth) as [factor [Hfactor Hrelation]].
  pose proof (karr_inject_nonzero a Ha) as HaQ.
  pose proof (karr_inject_nonzero factor Hfactor) as HfactorQ.
  unfold karr_models in *. setoid_rewrite Hp in Hrelation.
  split; intro Hmodel.
  - apply (proj1 (Qmult_inj_l _ _ (inject_Z a) HaQ)).
    setoid_rewrite Hmodel in Hrelation. nra.
  - apply (proj1 (Qmult_inj_l _ _ (inject_Z factor) HfactorQ)).
    setoid_rewrite Hmodel in Hrelation. nra.
Qed.

(** A zero leading coefficient makes the leading store coordinate irrelevant. *)
Lemma karr_eval_tail_zero : forall q qs r, karr_head r = 0%Z ->
  (karr_eval (q :: qs) (kcoeff r) == karr_eval qs (kcoeff (karr_tail r)))%Q.
Proof.
  intros q qs [zs rhs ws sc] Hzero.
  destruct zs as [|z zs]; cbn [karr_head kcoeff] in Hzero;
    cbn [karr_tail kcoeff karr_eval tl]; [destruct qs; reflexivity|].
  subst z. ring.
Qed.

(** Removing a zero leading coefficient preserves the row's models. *)
Lemma karr_models_tail_zero : forall q qs r, karr_head r = 0%Z ->
  (karr_models (q :: qs) r <-> karr_models qs (karr_tail r)).
Proof.
  intros q qs r Hzero. unfold karr_models.
  setoid_rewrite (karr_eval_tail_zero q qs r Hzero). reflexivity.
Qed.

(** Restoring a leading zero does not constrain the leading store coordinate. *)
Lemma karr_models_restore : forall q qs r,
  (karr_models (q :: qs) (karr_restore r) <-> karr_models qs r).
Proof.
  intros q qs r. unfold karr_models, karr_restore.
  change ((0 * q + karr_eval qs (kcoeff r) == inject_Z (kright r))%Q <->
    (karr_eval qs (kcoeff r) == inject_Z (kright r))%Q).
  setoid_rewrite Qmult_0_l. setoid_rewrite Qplus_0_l. reflexivity.
Qed.

(** Pointwise equivalence lifts through a mapped finite conjunction. *)
Lemma karr_Forall_map_iff : forall A B (f : A -> B) (P : B -> Prop) (R : A -> Prop) xs,
  (forall x, In x xs -> (P (f x) <-> R x)) ->
  (Forall P (map f xs) <-> Forall R xs).
Proof.
  intros A B f P R xs Hpoint. rewrite !Forall_forall. split; intros Hmodels x Hin.
  - apply (proj1 (Hpoint x Hin)). apply Hmodels. now apply in_map.
  - apply in_map_iff in Hin as [y [Heq Hin]]. subst x.
    apply (proj2 (Hpoint y Hin)). now apply Hmodels.
Qed.

(** Restoring zeros lifts all tail models to models of the restored rows. *)
Lemma karr_Forall_restore : forall q qs rs,
  (Forall (karr_models (q :: qs)) (map karr_restore rs) <->
    Forall (karr_models qs) rs).
Proof.
  intros q qs rs. apply karr_Forall_map_iff. intros r _. apply karr_models_restore.
Qed.

(** Permuting a row list preserves simultaneous rational satisfaction. *)
Lemma karr_models_permutation : forall qs rs ss, Permutation rs ss ->
  (Forall (karr_models qs) rs <-> Forall (karr_models qs) ss).
Proof.
  intros qs rs ss Hperm. split; intro Hmodels.
  - eapply Permutation_Forall; [exact Hperm|exact Hmodels].
  - eapply Permutation_Forall; [apply Permutation_sym; exact Hperm|exact Hmodels].
Qed.

(** Eliminating the leading coordinate preserves a row once the pivot is satisfied. *)
Lemma karr_reduce_tail_models : forall q qs d p r,
  length (kcoeff r) = length (kcoeff p) -> karr_head p <> 0%Z ->
  karr_models (q :: qs) p ->
  (karr_models qs (karr_tail (karr_reduce d (karr_head p) (karr_head r) p r)) <->
    karr_models (q :: qs) r).
Proof.
  intros q qs d p r Hwidth Hpivot Hp.
  rewrite <- (karr_models_tail_zero q qs _ (karr_reduce_head_zero d p r)).
  now apply karr_reduce_models.
Qed.

(** The whole guarded elimination preserves every rational model of equally wide rows. *)
Lemma karr_bareiss_models : forall n d rs qs, length qs = n ->
  Forall (fun r => length (kcoeff r) = n) rs ->
  (Forall (karr_models qs) (karr_bareiss n d rs) <-> Forall (karr_models qs) rs).
Proof.
  intro n. induction n as [|n IH]; intros d rs qs Hlength Hwidth.
  - reflexivity.
  - destruct qs as [|q qs]; cbn [length] in Hlength; [discriminate|].
    assert (Htail_length : length qs = n) by lia.
    cbn [karr_bareiss]. destruct (karr_pivot rs) as [[p rest]|] eqn:Hpivot.
    + destruct (karr_pivot_some rs p rest Hpivot) as [Hhead Hperm].
      assert (Hordered : Forall (fun r => length (kcoeff r) = S n) (p :: rest)).
      { eapply Permutation_Forall; [exact Hperm|exact Hwidth]. }
      inversion Hordered as [|p' rest' Hp Hrest]; subst p' rest'.
      set (reduced := map (fun r =>
        karr_tail (karr_reduce d (karr_head p) (karr_head r) p r)) rest).
      assert (Hreduced : Forall (fun r => length (kcoeff r) = n) reduced).
      { apply Forall_forall. intros r Hin. unfold reduced in Hin.
        apply in_map_iff in Hin as [s [Heq Hin]]. subst r.
        apply karr_tail_width. rewrite karr_reduce_width.
        - exact (proj1 (Forall_forall _ _) Hrest s Hin).
        - rewrite Hp. exact (proj1 (Forall_forall _ _) Hrest s Hin). }
      rewrite (karr_models_permutation (q :: qs) rs (p :: rest) Hperm).
      rewrite !Forall_cons_iff, karr_Forall_restore, (IH _ _ _ Htail_length Hreduced).
      assert (Hpoint : karr_models (q :: qs) p ->
        (Forall (karr_models qs) reduced <-> Forall (karr_models (q :: qs)) rest)).
      { intro Hmodelp. unfold reduced. apply karr_Forall_map_iff. intros r Hin.
        apply karr_reduce_tail_models; [|exact Hhead|exact Hmodelp].
        rewrite Hp. exact (proj1 (Forall_forall _ _) Hrest r Hin). }
      split; intros [Hmodelp Hmodels]; split; [exact Hmodelp| |exact Hmodelp|].
      * now apply (proj1 (Hpoint Hmodelp)).
      * now apply (proj2 (Hpoint Hmodelp)).
    + assert (Htail_width : Forall (fun r => length (kcoeff r) = n) (map karr_tail rs)).
      { apply Forall_forall. intros r Hin. apply in_map_iff in Hin as [s [Heq Hin]].
        subst r. apply karr_tail_width. exact (proj1 (Forall_forall _ _) Hwidth s Hin). }
      rewrite karr_Forall_restore, (IH d _ qs Htail_length Htail_width).
      apply karr_Forall_map_iff. intros r Hin. symmetry. apply karr_models_tail_zero.
      exact (proj1 (Forall_forall _ _) (karr_pivot_none rs Hpivot) r Hin).
Qed.

(** A reduced target has zero coefficients at every pivot of the basis. *)
Definition karr_reduced (rs : list karr_row) (zs : list Z) : Prop :=
  forall r i a, In r rs -> karr_first (kcoeff r) = Some (i, a) -> karr_nth i zs = 0%Z.

(** A nonzero head is the first coefficient of a row. *)
Lemma karr_first_head : forall r, karr_head r <> 0%Z ->
  karr_first (kcoeff r) = Some (0%nat, karr_head r).
Proof.
  intros [zs rhs ws sc] Hnonzero. destruct zs as [|z zs].
  - exfalso. apply Hnonzero. reflexivity.
  - cbn [karr_head kcoeff] in *. cbn [karr_first].
    assert (Hz : Z.eqb z 0 = false) by now apply Z.eqb_neq.
    now rewrite Hz.
Qed.

(** A restored zero shifts every existing pivot by one position. *)
Lemma karr_first_restore : forall r i a, karr_first (kcoeff r) = Some (i, a) ->
  karr_first (kcoeff (karr_restore r)) = Some (S i, a).
Proof.
  intros r i a Hfirst. cbn [karr_restore kcoeff karr_first]. now rewrite Hfirst.
Qed.

(** Every pivot of a restored row comes from its unshifted row. *)
Lemma karr_first_restore_inv : forall r i a,
  karr_first (kcoeff (karr_restore r)) = Some (i, a) ->
  exists j, i = S j /\ karr_first (kcoeff r) = Some (j, a).
Proof.
  intros r i a Hfirst. cbn [karr_restore kcoeff karr_first] in Hfirst.
  destruct (karr_first (kcoeff r)) as [[j b]|] eqn:Htail; [|discriminate].
  injection Hfirst as Hindex Hvalue. subst i a. exists j. split; reflexivity.
Qed.

(** Every coordinate before the first nonzero coefficient vanishes. *)
Lemma karr_first_before : forall zs i a,
  karr_first zs = Some (i, a) -> forall j, j < i -> karr_nth j zs = 0%Z.
Proof.
  intro zs. induction zs as [|z zs IH]; intros i a Hfirst j Hbefore;
    cbn [karr_first] in Hfirst; [discriminate|].
  destruct (Z.eqb z 0) eqn:Hzero.
  - apply Z.eqb_eq in Hzero. subst z.
    destruct (karr_first zs) as [[k b]|] eqn:Htail; [|discriminate].
    injection Hfirst as Hindex Hvalue. subst i a.
    destruct j as [|j]; cbn [karr_nth]; [reflexivity|].
    apply (IH k b); [auto|lia].
  - injection Hfirst as Hindex Hvalue. subst i a. lia.
Qed.

(** Failure to find a first coefficient means every coordinate vanishes. *)
Lemma karr_first_none : forall zs, karr_first zs = None ->
  forall i, karr_nth i zs = 0%Z.
Proof.
  intro zs. induction zs as [|z zs IH]; intros Hnone i.
  - destruct i; reflexivity.
  - cbn [karr_first] in Hnone. destruct (Z.eqb z 0) eqn:Hzero; [|discriminate].
    apply Z.eqb_eq in Hzero. subst z.
    destruct (karr_first zs) as [[j a]|] eqn:Htail; [discriminate|].
    destruct i as [|i]; cbn [karr_nth]; [reflexivity|].
    apply IH. auto.
Qed.

(** Coordinate lookup commutes with integer coefficient scaling, including absent positions. *)
Lemma karr_nth_scale : forall factor zs i,
  karr_nth i (map (fun z => (factor * z)%Z) zs) = (factor * karr_nth i zs)%Z.
Proof.
  intros factor zs. induction zs as [|z zs IH]; intros [|i];
    cbn [map karr_nth]; try ring. apply IH.
Qed.

(** Checked division preserves a zero coordinate in every branch. *)
Lemma karr_divide_coordinate_zero : forall divisor r i,
  karr_nth i (kcoeff r) = 0%Z -> karr_nth i (kcoeff (karr_divide divisor r)) = 0%Z.
Proof.
  intros divisor r i Hzero.
  destruct (karr_divide_factor divisor r) as [factor [Hnonzero [Hcoeff _]]].
  pose proof (f_equal (karr_nth i) Hcoeff) as Hcoordinate.
  rewrite karr_nth_scale, Hzero in Hcoordinate. nia.
Qed.

(** Crossing two rows preserves every coordinate zero in both, even for unequal widths. *)
Lemma karr_nth_cross_zero : forall i a b xs ys,
  karr_nth i xs = 0%Z -> karr_nth i ys = 0%Z ->
  karr_nth i (karr_cross a b xs ys) = 0%Z.
Proof.
  intro i. induction i as [|i IH]; intros a b [|x xs] [|y ys] Hx Hy;
    cbn [karr_nth karr_cross] in *; try reflexivity.
  - rewrite Hx, Hy. ring.
  - now apply IH.
Qed.

(** Crossing at a selected coordinate cancels it even if the lists are truncated. *)
Lemma karr_nth_cross_cancel : forall i xs ys,
  karr_nth i (karr_cross (karr_nth i ys) (karr_nth i xs) xs ys) = 0%Z.
Proof.
  intro i. induction i as [|i IH]; intros [|x xs] [|y ys];
    cbn [karr_nth karr_cross]; try reflexivity.
  - ring.
  - apply IH.
Qed.

(** A reduction preserves every coordinate zero in both of its rows. *)
Lemma karr_reduce_coordinate_zero : forall divisor a b p r i,
  karr_nth i (kcoeff p) = 0%Z -> karr_nth i (kcoeff r) = 0%Z ->
  karr_nth i (kcoeff (karr_reduce divisor a b p r)) = 0%Z.
Proof.
  intros divisor a b p r i Hp Hr. unfold karr_reduce.
  apply karr_divide_coordinate_zero. cbn [kcoeff]. now apply karr_nth_cross_zero.
Qed.

(** Reducing against a row's first coefficient cancels that pivot coordinate. *)
Lemma karr_reduce_coordinate_cancel : forall divisor p r i a,
  karr_first (kcoeff p) = Some (i, a) ->
  karr_nth i (kcoeff (karr_reduce divisor a (karr_nth i (kcoeff r)) p r)) = 0%Z.
Proof.
  intros divisor p r i a Hfirst. unfold karr_reduce.
  apply karr_divide_coordinate_zero. cbn [kcoeff].
  rewrite <- (karr_first_nth (kcoeff p) i a Hfirst). apply karr_nth_cross_cancel.
Qed.

(** A coordinate absent from every basis row stays zero during target reduction. *)
Lemma karr_target_coordinate_zero : forall rs previous r i,
  Forall (fun p => karr_nth i (kcoeff p) = 0%Z) rs ->
  karr_nth i (kcoeff r) = 0%Z ->
  karr_nth i (kcoeff (karr_target rs previous r)) = 0%Z.
Proof.
  intro rs. induction rs as [|p rs IH]; intros previous r i Hbasis Hrow; [exact Hrow|].
  inversion Hbasis as [|p' rs' Hp Hrest]; subst p' rs'.
  cbn [karr_target]. destruct (karr_first (kcoeff p)) as [[j a]|].
  - apply IH; [exact Hrest|]. now apply karr_reduce_coordinate_zero.
  - now apply IH.
Qed.

(** Nonzero pivots advance strictly through the list, while zero rows may occur anywhere. *)
Inductive karr_ordered : list karr_row -> Prop :=
  | karr_ordered_nil : karr_ordered []
  | karr_ordered_cons : forall p rs,
      karr_ordered rs ->
      (forall i a q j b, karr_first (kcoeff p) = Some (i, a) ->
        In q rs -> karr_first (kcoeff q) = Some (j, b) -> i < j) ->
      karr_ordered (p :: rs).

(** Lists with no nonzero pivots satisfy the ordering condition. *)
Lemma karr_ordered_zero : forall rs,
  Forall (fun r => karr_first (kcoeff r) = None) rs -> karr_ordered rs.
Proof.
  intros rs Hzero. induction Hzero as [|p rs Hp Hrest IH].
  - constructor.
  - constructor; [exact IH|]. intros i a q j b Hfirst _ _.
    rewrite Hp in Hfirst. discriminate.
Qed.

(** Restoring a zero shifts all pivots together and preserves their strict order. *)
Lemma karr_ordered_restore : forall rs,
  karr_ordered rs -> karr_ordered (map karr_restore rs).
Proof.
  intros rs Hordered. induction Hordered as [|p rs Hordered IH Hbefore]; cbn [map].
  - constructor.
  - constructor; [exact IH|]. intros i a q j b Hp Hin Hq.
    apply in_map_iff in Hin as [s [Hsame Hin]]. subst q.
    destruct (karr_first_restore_inv p i a Hp) as [ip [Hi Hpi]].
    destruct (karr_first_restore_inv s j b Hq) as [iq [Hj Hqi]].
    subst i j. pose proof (Hbefore ip a s iq b Hpi Hin Hqi). lia.
Qed.

(** The recursive echelon shape entails strictly ordered pivot positions. *)
Lemma karr_echelon_ordered : forall n rs, karr_echelon n rs -> karr_ordered rs.
Proof.
  intros n rs Hechelon. induction Hechelon as
    [rs Hempty|n rs Hechelon IH|n p rs Hwidth Hnonzero Hechelon IH].
  - apply karr_ordered_zero. apply Forall_forall. intros r Hin.
    rewrite (proj1 (Forall_forall _ _) Hempty r Hin). reflexivity.
  - now apply karr_ordered_restore.
  - constructor; [now apply karr_ordered_restore|]. intros i a q j b Hp Hin Hq.
    rewrite (karr_first_head p Hnonzero) in Hp. injection Hp as Hindex Hvalue. subst i a.
    apply in_map_iff in Hin as [s [Hsame Hin]]. subst q.
    destruct (karr_first_restore_inv s j b Hq) as [k [Hj _]]. lia.
Qed.

(** Later pivots leave each canceled earlier pivot at zero. *)
Lemma karr_target_ordered_reduced : forall rs, karr_ordered rs ->
  forall previous r, karr_reduced rs (kcoeff (karr_target rs previous r)).
Proof.
  intros rs Hordered. induction Hordered as [|p rs Hordered IH Hbefore]; intros previous r.
  - intros q i a Hin. contradiction.
  - cbn [karr_target]. destruct (karr_first (kcoeff p)) as [[i a]|] eqn:Hp.
    + assert (Hlater : Forall (fun q => karr_nth i (kcoeff q) = 0%Z) rs).
      { apply Forall_forall. intros q Hin.
        destruct (karr_first (kcoeff q)) as [[j b]|] eqn:Hq.
        - apply (karr_first_before (kcoeff q) j b Hq i).
          eapply Hbefore; [auto|exact Hin|exact Hq].
        - now apply karr_first_none. }
      assert (Hpivot : karr_nth i
        (kcoeff (karr_target rs a
          (karr_reduce previous a (karr_nth i (kcoeff r)) p r))) = 0%Z).
      { apply karr_target_coordinate_zero; [exact Hlater|].
        now apply karr_reduce_coordinate_cancel. }
      intros q j b Hin Hq. destruct Hin as [Hsame|Hin].
      * subst q. rewrite Hp in Hq. injection Hq as Hindex Hvalue. subst j b. exact Hpivot.
      * exact (IH a (karr_reduce previous a (karr_nth i (kcoeff r)) p r) q j b Hin Hq).
    + intros q j b Hin Hq. destruct Hin as [Hsame|Hin].
      * subst q. rewrite Hp in Hq. discriminate.
      * exact (IH previous r q j b Hin Hq).
Qed.

(** Target reduction against an echelon basis zeros every basis pivot. *)
Lemma karr_target_reduced : forall n rs previous r,
  karr_echelon n rs -> karr_reduced rs (kcoeff (karr_target rs previous r)).
Proof.
  intros n rs previous r Hechelon. apply karr_target_ordered_reduced.
  now apply karr_echelon_ordered with (n := n).
Qed.

(** Every row in an echelon basis has the recorded coordinate width. *)
Lemma karr_echelon_width : forall n rs, karr_echelon n rs ->
  Forall (fun r => length (kcoeff r) = n) rs.
Proof.
  intros n rs Hechelon. induction Hechelon as
    [rs Hempty|n rs Hechelon IH|n p rs Hwidth Hnonzero Hechelon IH].
  - apply Forall_forall. intros r Hin.
    rewrite (proj1 (Forall_forall _ _) Hempty r Hin). reflexivity.
  - apply Forall_forall. intros r Hin.
    apply in_map_iff in Hin as [s [Hsame Hin]]. subst r.
    rewrite karr_restore_width, (proj1 (Forall_forall _ _) IH s Hin). reflexivity.
  - constructor; [exact Hwidth|]. apply Forall_forall. intros r Hin.
    apply in_map_iff in Hin as [s [Hsame Hin]]. subst r.
    rewrite karr_restore_width, (proj1 (Forall_forall _ _) IH s Hin). reflexivity.
Qed.

(** Reducing a target against equally wide basis rows preserves its width. *)
Lemma karr_target_width : forall n rs previous r,
  Forall (fun p => length (kcoeff p) = n) rs -> length (kcoeff r) = n ->
  length (kcoeff (karr_target rs previous r)) = n.
Proof.
  intros n rs. induction rs as [|p rs IH]; intros previous r Hbasis Hwidth; [exact Hwidth|].
  inversion Hbasis as [|p' rs' Hp Hrest]; subst p' rs'.
  cbn [karr_target]. destruct (karr_first (kcoeff p)) as [[i a]|].
  - apply IH; [exact Hrest|]. rewrite karr_reduce_width; [exact Hwidth|lia].
  - now apply IH.
Qed.

(** A zero coefficient row is consistent exactly when its right-hand side vanishes. *)
Definition karr_zero_right (rs : list karr_row) : Prop :=
  Forall (fun r => karr_zero r = true -> kright r = 0%Z) rs.

(** Removing a leading basis row preserves reduction at the remaining pivots. *)
Lemma karr_reduced_tail : forall p rs zs,
  karr_reduced (p :: rs) zs -> karr_reduced rs zs.
Proof.
  intros p rs zs Hreduced r i a Hin Hfirst.
  apply (Hreduced r i a); [now right|exact Hfirst].
Qed.

(** Restored basis pivots constrain only the tail of a reduced target. *)
Lemma karr_reduced_restore : forall rs z zs,
  karr_reduced (map karr_restore rs) (z :: zs) -> karr_reduced rs zs.
Proof.
  intros rs z zs Hreduced r i a Hin Hfirst.
  exact (Hreduced (karr_restore r) (S i) a (in_map karr_restore rs r Hin)
    (karr_first_restore r i a Hfirst)).
Qed.

(** Zero-row consistency is unchanged by restoring leading zero coefficients. *)
Lemma karr_zero_right_restore : forall rs,
  karr_zero_right (map karr_restore rs) <-> karr_zero_right rs.
Proof.
  intro rs. unfold karr_zero_right. apply karr_Forall_map_iff. intros r _.
  change ((karr_zero r = true -> kright r = 0%Z) <->
    (karr_zero r = true -> kright r = 0%Z)). reflexivity.
Qed.

(** Solving one nonzero leading coefficient determines its store coordinate. *)
Definition karr_head_value (qs : list Q) (p : karr_row) : Q :=
  ((inject_Z (kright p) - karr_eval qs (tl (kcoeff p))) / inject_Z (karr_head p))%Q.

(** Back substitution satisfies its pivot row. *)
Lemma karr_solve_head : forall qs p, karr_head p <> 0%Z ->
  karr_models (karr_head_value qs p :: qs) p.
Proof.
  intros qs [zs rhs ws sc] Hnonzero. destruct zs as [|z zs].
  - exfalso. apply Hnonzero. reflexivity.
  - cbn [karr_head kcoeff] in Hnonzero.
    unfold karr_models, karr_head_value. cbn [karr_head kcoeff kright tl karr_eval].
    field. now apply karr_inject_nonzero.
Qed.

(** A triangular basis with no false constant row has a rational model. *)
Lemma karr_echelon_model : forall n rs, karr_echelon n rs -> karr_zero_right rs ->
  exists qs, length qs = n /\ Forall (karr_models qs) rs.
Proof.
  intros n rs Hechelon. induction Hechelon as
    [rs Hempty|n rs Hechelon IH|n p rs Hwidth Hnonzero Hechelon IH]; intro Hzero.
  - exists []. split; [reflexivity|]. apply Forall_forall. intros r Hin.
    pose proof (proj1 (Forall_forall _ _) Hempty r Hin) as Hcoeff.
    pose proof (proj1 (Forall_forall _ _) Hzero r Hin) as Hright.
    assert (Hrowzero : karr_zero r = true).
    { unfold karr_zero. now rewrite Hcoeff. }
    specialize (Hright Hrowzero). unfold karr_models. rewrite Hright. reflexivity.
  - apply (proj1 (karr_zero_right_restore rs)) in Hzero.
    destruct (IH Hzero) as [qs [Hlength Hmodels]].
    exists (0%Q :: qs). split; [cbn [length]; now rewrite Hlength|].
    now apply (proj2 (karr_Forall_restore 0%Q qs rs)).
  - assert (Htail : karr_zero_right rs).
    { apply (proj1 (karr_zero_right_restore rs)). now apply Forall_inv_tail in Hzero. }
    destruct (IH Htail) as [qs [Hlength Hmodels]].
    exists (karr_head_value qs p :: qs). split; [cbn [length]; now rewrite Hlength|].
    constructor; [now apply karr_solve_head|].
    now apply (proj2 (karr_Forall_restore (karr_head_value qs p) qs rs)).
Qed.

(** A nonzero reduced target can attain any rational value while the basis remains true. *)
Lemma karr_echelon_countermodel : forall n rs, karr_echelon n rs ->
  karr_zero_right rs -> forall zs, length zs = n -> karr_reduced rs zs ->
  forallb (Z.eqb 0) zs = false -> forall value : Q,
  exists qs, length qs = n /\ Forall (karr_models qs) rs /\
    (karr_eval qs zs == value)%Q.
Proof.
  intros n rs Hechelon. induction Hechelon as
    [rs Hempty|n rs Hechelon IH|n p rs Hwidth Hnonzero Hechelon IH];
    intros Hzero zs Hlength Hreduced Hnotzero value.
  - destruct zs as [|z zs].
    + change (true = false) in Hnotzero. discriminate.
    + cbn [length] in Hlength. discriminate.
  - destruct zs as [|z zs]; cbn [length] in Hlength; [discriminate|].
    assert (Htail_length : length zs = n) by lia.
    apply (proj1 (karr_zero_right_restore rs)) in Hzero.
    pose proof (karr_reduced_restore rs z zs Hreduced) as Htail_reduced.
    change (Z.eqb 0 z && forallb (Z.eqb 0) zs = false) in Hnotzero.
    destruct (Z.eqb 0 z) eqn:Hzero_z.
    + apply Z.eqb_eq in Hzero_z. subst z. cbn [andb] in Hnotzero.
      destruct (IH Hzero zs Htail_length Htail_reduced Hnotzero value)
        as [qs [Hqlength [Hmodels Hvalue]]].
      exists (0%Q :: qs). split; [cbn [length]; now rewrite Hqlength|].
      split; [now apply (proj2 (karr_Forall_restore 0%Q qs rs))|].
      change (0 * 0 + karr_eval qs zs == value)%Q. setoid_rewrite Hvalue. ring.
    + apply Z.eqb_neq in Hzero_z.
      destruct (karr_echelon_model n rs Hechelon Hzero) as [qs [Hqlength Hmodels]].
      set (q := ((value - karr_eval qs zs) / inject_Z z)%Q).
      exists (q :: qs). split; [cbn [length]; now rewrite Hqlength|].
      split; [now apply (proj2 (karr_Forall_restore q qs rs))|].
      change (inject_Z z * q + karr_eval qs zs == value)%Q.
      unfold q. field. apply karr_inject_nonzero. lia.
  - destruct zs as [|z zs]; cbn [length] in Hlength; [discriminate|].
    assert (Htail_length : length zs = n) by lia.
    assert (Htail_zero : karr_zero_right rs).
    { apply (proj1 (karr_zero_right_restore rs)). now apply Forall_inv_tail in Hzero. }
    assert (Hzero_z : z = 0%Z).
    { exact (Hreduced p 0 (karr_head p) (or_introl eq_refl)
        (karr_first_head p Hnonzero)). }
    pose proof (karr_reduced_restore rs z zs (karr_reduced_tail p _ _ Hreduced))
      as Htail_reduced.
    subst z. change (forallb (Z.eqb 0) zs = false) in Hnotzero.
    destruct (IH Htail_zero zs Htail_length Htail_reduced Hnotzero value)
      as [qs [Hqlength [Hmodels Hvalue]]].
    exists (karr_head_value qs p :: qs). split; [cbn [length]; now rewrite Hqlength|].
    split.
    + constructor; [now apply karr_solve_head|].
      now apply (proj2 (karr_Forall_restore (karr_head_value qs p) qs rs)).
    + change (0 * karr_head_value qs p + karr_eval qs zs == value)%Q.
      setoid_rewrite Hvalue. ring.
Qed.

(** Equally long prefixes can be evaluated independently of their suffixes. *)
Lemma karr_eval_app : forall qs zs, length qs = length zs -> forall ps ts,
  (karr_eval (qs ++ ps) (zs ++ ts) == karr_eval qs zs + karr_eval ps ts)%Q.
Proof.
  intro qs. induction qs as [|q qs IH]; intros [|z zs] Hlength ps ts;
    cbn [length] in Hlength; try discriminate.
  - cbn [app karr_eval]. ring.
  - cbn [app karr_eval]. setoid_rewrite (IH zs ltac:(lia) ps ts). ring.
Qed.

(** Zero coordinate values annihilate every coefficient vector. *)
Lemma karr_eval_zero_values : forall n zs,
  (karr_eval (repeat 0%Q n) zs == 0)%Q.
Proof.
  intro n. induction n as [|n IH]; intros [|z zs]; cbn [repeat karr_eval]; try ring.
  setoid_rewrite IH. ring.
Qed.

(** Zero coefficients evaluate to zero for any finite coordinate values. *)
Lemma karr_eval_zero_coefficients : forall qs n,
  (karr_eval qs (repeat 0%Z n) == 0)%Q.
Proof.
  intro qs. induction qs as [|q qs IH]; intros [|n]; cbn [repeat karr_eval]; try ring.
  change (0 * q + karr_eval qs (repeat 0%Z n) == 0)%Q.
  setoid_rewrite IH. ring.
Qed.

(** Negating every coefficient negates its rational evaluation. *)
Lemma karr_eval_opp : forall qs zs,
  (karr_eval qs (map Z.opp zs) == - karr_eval qs zs)%Q.
Proof.
  intro qs. induction qs as [|q qs IH]; intros [|z zs];
    cbn [map karr_eval]; try ring.
  rewrite inject_Z_opp. setoid_rewrite IH. ring.
Qed.

(** A left seed tests only the first block and its homogeneous coordinate. *)
Lemma karr_eval_hull_left : forall qs zs, length qs = length zs ->
  forall q tail b n,
  (karr_eval ((qs ++ [q]) ++ tail) (zs ++ (- b)%Z :: repeat 0%Z n) ==
    karr_eval qs zs - inject_Z b * q)%Q.
Proof.
  intros qs zs Hlength q tail b n. rewrite <- app_assoc.
  setoid_rewrite (karr_eval_app qs zs Hlength (q :: tail)
    ((- b)%Z :: repeat 0%Z n)).
  cbn [karr_eval]. rewrite inject_Z_opp.
  setoid_rewrite karr_eval_zero_coefficients. ring.
Qed.

(** A right seed compares the two coordinate blocks and their homogeneous values. *)
Lemma karr_eval_hull_right : forall qs ps zs,
  length qs = length zs -> length ps = length zs -> forall q p b,
  (karr_eval ((qs ++ [q]) ++ (ps ++ [p]))
    (map Z.opp zs ++ b :: zs ++ [b]) ==
    - karr_eval qs zs + inject_Z b * q +
      karr_eval ps zs + inject_Z b * p)%Q.
Proof.
  intros qs ps zs Hleft Hright q p b. rewrite <- app_assoc.
  assert (Hopp : length qs = length (map Z.opp zs)) by now rewrite length_map.
  setoid_rewrite (karr_eval_app qs (map Z.opp zs) Hopp
    (q :: ps ++ [p]) (b :: zs ++ [b])).
  cbn [karr_eval]. setoid_rewrite karr_eval_opp.
  setoid_rewrite (karr_eval_app ps zs Hright [p] [b]).
  cbn [karr_eval]. ring.
Qed.

(** Homogeneous seed equations remain homogeneous after guarded elimination. *)
Lemma karr_bareiss_zero_right : forall n d rows,
  Forall (fun r => length (kcoeff r) = n) rows ->
  Forall (fun r => kright r = 0%Z) rows ->
  Forall (fun r => kright r = 0%Z) (karr_bareiss n d rows).
Proof.
  intros n d rows Hwidth Hzero.
  assert (Hmodels : Forall (karr_models (repeat 0%Q n)) rows).
  { apply Forall_forall. intros r Hin. unfold karr_models.
    rewrite (proj1 (Forall_forall _ _) Hzero r Hin).
    setoid_rewrite karr_eval_zero_values. reflexivity. }
  pose proof (proj2 (karr_bareiss_models n d rows (repeat 0%Q n)
    (repeat_length 0%Q n) Hwidth) Hmodels) as Hbasis.
  apply Forall_forall. intros r Hin.
  pose proof (proj1 (Forall_forall _ _) Hbasis r Hin) as Hmodel.
  unfold karr_models in Hmodel. setoid_rewrite karr_eval_zero_values in Hmodel.
  apply (proj1 (inject_Z_injective _ _)). symmetry. exact Hmodel.
Qed.

(** A final negative unit coordinate interprets the last coefficient as a right-hand side. *)
Lemma karr_eval_extra_rhs : forall qs zs,
  length zs = S (length qs) ->
  (karr_eval (qs ++ [(-1)%Q]) zs ==
    karr_eval qs zs - inject_Z (karr_nth (length qs) zs))%Q.
Proof.
  intro qs. induction qs as [|q qs IH]; intros [|z zs] Hlength;
    cbn [length] in Hlength; try discriminate.
  - assert (Hzs : zs = []) by (apply length_zero_iff_nil; lia). subst zs.
    change (inject_Z z * (-1) + 0 == 0 - inject_Z z)%Q. ring.
  - change (inject_Z z * q + karr_eval (qs ++ [(-1)%Q]) zs ==
      inject_Z z * q + karr_eval qs zs - inject_Z (karr_nth (length qs) zs))%Q.
    setoid_rewrite (IH zs ltac:(lia)). ring.
Qed.

(** Zero auxiliary coefficients make their concrete coordinate values irrelevant. *)
Lemma karr_eval_zero_prefix : forall aux out zs,
  length aux <= length zs ->
  forallb (Z.eqb 0) (firstn (length aux) zs) = true ->
  (karr_eval (aux ++ out) zs == karr_eval out (skipn (length aux) zs))%Q.
Proof.
  intro aux. induction aux as [|q aux IH]; intros out [|z zs] Hlength Hzero;
    try reflexivity.
  - cbn [length] in Hlength. lia.
  - cbn [length firstn forallb] in Hzero.
    apply andb_true_iff in Hzero as [Hz Htail]. apply Z.eqb_eq in Hz. subst z.
    change (0 * q + karr_eval (aux ++ out) zs ==
      karr_eval out (skipn (length aux) zs))%Q.
    setoid_rewrite (IH out zs ltac:(cbn [length] in Hlength; lia) Htail). ring.
Qed.

Lemma karr_values_ne_app : forall A (tr : trie_ne A) acc,
  karr_values_ne tr acc = karr_values_ne tr [] ++ acc.
Proof.
  intros A tr.
  induction tr as [r IHr|a|a r IHr|l IHl|l IHl r IHr|l IHl a|l IHl a r IHr];
    intro acc; cbn [karr_values_ne].
  - apply IHr.
  - reflexivity.
  - rewrite (IHr acc). reflexivity.
  - apply IHl.
  - rewrite (IHl (karr_values_ne r acc)), (IHr acc),
      (IHl (karr_values_ne r [])). now rewrite app_assoc.
  - rewrite (IHl (a :: acc)), (IHl [a]). now rewrite <- app_assoc.
  - rewrite (IHl (a :: karr_values_ne r acc)), (IHr acc),
      (IHl (a :: karr_values_ne r [])). now rewrite <- app_assoc.
Qed.

Lemma karr_values_node : forall A (l r : ptrie A) o,
  karr_values (PTrieCode.node l o r) =
    karr_values l ++ match o with Some a => a :: karr_values r | None => karr_values r end.
Proof.
  intros A [|l] [|r] [a|]; cbn [PTrieCode.node karr_values karr_values_ne];
    try rewrite karr_values_ne_app; now rewrite ?app_nil_r.
Qed.

Definition karr_zsum {A} (f : A -> Z) (xs : list A) : Z :=
  fold_right (fun a z => (f a + z)%Z) 0%Z xs.

Definition karr_zmass {A} (f : A -> Z) (tr : ptrie A) : Z :=
  karr_zsum f (karr_values tr).

Definition karr_zoption {A} (f : A -> Z) (o : option A) : Z :=
  match o with Some a => f a | None => 0%Z end.

Lemma karr_zsum_app : forall A (f : A -> Z) xs ys,
  karr_zsum f (xs ++ ys) = (karr_zsum f xs + karr_zsum f ys)%Z.
Proof.
  intros A f xs. unfold karr_zsum. induction xs as [|a xs IH]; intro ys; cbn.
  - reflexivity.
  - rewrite IH. ring.
Qed.

Lemma karr_zmass_node : forall A (f : A -> Z) l o r,
  karr_zmass f (PTrieCode.node l o r) =
    (karr_zmass f l + karr_zoption f o + karr_zmass f r)%Z.
Proof.
  intros A f l [a|] r; unfold karr_zmass; rewrite karr_values_node, karr_zsum_app;
    unfold karr_zsum; cbn [fold_right karr_zoption]; ring.
Qed.

Lemma karr_zmass_view : forall A (f : A -> Z) tr,
  karr_zmass f tr =
    (karr_zmass f (PTrieCode.left tr) + karr_zoption f (PTrieCode.value tr) +
     karr_zmass f (PTrieCode.right tr))%Z.
Proof.
  intros A f tr.
  assert (Hnode : PTrieCode.node (PTrieCode.left tr) (PTrieCode.value tr)
    (PTrieCode.right tr) = tr).
  { destruct tr as [|n]; [reflexivity|destruct n; reflexivity]. }
  rewrite <- Hnode at 1. apply karr_zmass_node.
Qed.

Lemma karr_zmass_set : forall A (f : A -> Z) p a tr,
  karr_zmass f (PTrieCode.set p a tr) =
    (karr_zmass f tr + f a - karr_zoption f (PTrieCode.get p tr))%Z.
Proof.
  intros A f p a. unfold PTrieCode.set.
  induction p as [p IH|p IH|]; intro tr; cbn [PTrieCode.replace].
  - rewrite karr_zmass_node, IH, (karr_zmass_view A f tr).
    unfold PTrieCode.get, PTrieCode.left, PTrieCode.right, PTrieCode.value.
    cbn [trie_get]. ring.
  - rewrite karr_zmass_node, IH, (karr_zmass_view A f tr).
    unfold PTrieCode.get, PTrieCode.left, PTrieCode.right, PTrieCode.value.
    cbn [trie_get]. ring.
  - rewrite karr_zmass_node, (karr_zmass_view A f tr).
    unfold PTrieCode.get, PTrieCode.left, PTrieCode.right, PTrieCode.value.
    cbn [trie_get karr_zoption]. ring.
Qed.

Definition karr_qsum {A} (f : A -> Q) (xs : list A) : Q :=
  fold_right (fun a q => (f a + q)%Q) 0%Q xs.

Definition karr_qmass {A} (f : A -> Q) (tr : ptrie A) : Q :=
  karr_qsum f (karr_values tr).

Definition karr_qoption {A} (f : A -> Q) (o : option A) : Q :=
  match o with Some a => f a | None => 0%Q end.

Definition karr_eval_coef_Q {X} (v : X -> Q) (xs : list (X * Z)) : Q :=
  karr_qsum (fun p => (inject_Z (snd p) * v (fst p))%Q) xs.

Lemma karr_qsum_app : forall A (f : A -> Q) xs ys,
  (karr_qsum f (xs ++ ys) == karr_qsum f xs + karr_qsum f ys)%Q.
Proof.
  intros A f xs. induction xs as [|a xs IH]; intro ys.
  - change (karr_qsum f ys == 0 + karr_qsum f ys)%Q. ring.
  - change (f a + karr_qsum f (xs ++ ys) ==
      (f a + karr_qsum f xs) + karr_qsum f ys)%Q.
    setoid_rewrite IH. ring.
Qed.

Lemma karr_qmass_node : forall A (f : A -> Q) l o r,
  (karr_qmass f (PTrieCode.node l o r) ==
    karr_qmass f l + karr_qoption f o + karr_qmass f r)%Q.
Proof.
  intros A f l [a|] r; unfold karr_qmass; rewrite karr_values_node;
    setoid_rewrite karr_qsum_app; cbn [karr_qoption].
  - change (karr_qsum f (karr_values l) + (f a + karr_qsum f (karr_values r)) ==
      karr_qsum f (karr_values l) + f a + karr_qsum f (karr_values r))%Q. ring.
  - ring.
Qed.

Lemma karr_qmass_view : forall A (f : A -> Q) tr,
  (karr_qmass f tr ==
    karr_qmass f (PTrieCode.left tr) + karr_qoption f (PTrieCode.value tr) +
     karr_qmass f (PTrieCode.right tr))%Q.
Proof.
  intros A f tr.
  assert (Hnode : PTrieCode.node (PTrieCode.left tr) (PTrieCode.value tr)
    (PTrieCode.right tr) = tr).
  { destruct tr as [|n]; [reflexivity|destruct n; reflexivity]. }
  rewrite <- Hnode at 1. apply karr_qmass_node.
Qed.

Lemma karr_qmass_set : forall A (f : A -> Q) p a tr,
  (karr_qmass f (PTrieCode.set p a tr) ==
    karr_qmass f tr + f a - karr_qoption f (PTrieCode.get p tr))%Q.
Proof.
  intros A f p a. unfold PTrieCode.set.
  induction p as [p IH|p IH|]; intro tr; cbn [PTrieCode.replace].
  - setoid_rewrite karr_qmass_node. setoid_rewrite IH.
    setoid_rewrite (karr_qmass_view A f tr).
    change (karr_qmass f (PTrieCode.left tr) + karr_qoption f (PTrieCode.value tr) +
      (karr_qmass f (PTrieCode.right tr) + f a -
       karr_qoption f (PTrieCode.get p (PTrieCode.right tr))) ==
      karr_qmass f (PTrieCode.left tr) + karr_qoption f (PTrieCode.value tr) +
      karr_qmass f (PTrieCode.right tr) + f a -
       karr_qoption f (PTrieCode.get p (PTrieCode.right tr)))%Q. ring.
  - setoid_rewrite karr_qmass_node. setoid_rewrite IH.
    setoid_rewrite (karr_qmass_view A f tr).
    change (karr_qmass f (PTrieCode.left tr) + f a -
      karr_qoption f (PTrieCode.get p (PTrieCode.left tr)) +
      karr_qoption f (PTrieCode.value tr) + karr_qmass f (PTrieCode.right tr) ==
      karr_qmass f (PTrieCode.left tr) + karr_qoption f (PTrieCode.value tr) +
      karr_qmass f (PTrieCode.right tr) + f a -
       karr_qoption f (PTrieCode.get p (PTrieCode.left tr)))%Q. ring.
  - setoid_rewrite karr_qmass_node. setoid_rewrite (karr_qmass_view A f tr).
    change (karr_qmass f (PTrieCode.left tr) + f a + karr_qmass f (PTrieCode.right tr) ==
      karr_qmass f (PTrieCode.left tr) + karr_qoption f (PTrieCode.value tr) +
      karr_qmass f (PTrieCode.right tr) + f a - karr_qoption f (PTrieCode.value tr))%Q.
    ring.
Qed.

Lemma karr_fold_values_ne_append : forall A (tr : trie_ne A) acc,
  PTrieCode.fold_values_ne (fun acc a => acc ++ [a]) tr acc =
    acc ++ karr_values_ne tr [].
Proof.
  intros A tr.
  induction tr as [r IHr|a|a r IHr|l IHl|l IHl r IHr|l IHl a|l IHl a r IHr];
    intro acc; cbn [PTrieCode.fold_values_ne karr_values_ne].
  - apply IHr.
  - reflexivity.
  - rewrite IHr. now rewrite <- app_assoc.
  - apply IHl.
  - rewrite IHr, IHl, (karr_values_ne_app A l (karr_values_ne r [])).
    now rewrite app_assoc.
  - rewrite IHl, (karr_values_ne_app A l [a]). now rewrite app_assoc.
  - rewrite IHr, IHl, (karr_values_ne_app A l (a :: karr_values_ne r [])).
    now rewrite <- !app_assoc.
Qed.

Lemma karr_fold_values_append : forall A (tr : ptrie A) acc,
  PTrieCode.fold_values (fun acc a => acc ++ [a]) tr acc = acc ++ karr_values tr.
Proof.
  intros A [|n] acc; cbn [PTrieCode.fold_values karr_values].
  - now rewrite app_nil_r.
  - apply karr_fold_values_ne_append.
Qed.

Lemma karr_fold_left_values : forall A (xs : list (positive * A)) acc,
  fold_left (fun acc p => acc ++ [snd p]) xs acc = acc ++ map snd xs.
Proof.
  intros A xs. induction xs as [|[p a] xs IH]; intro acc; cbn [fold_left map snd].
  - now rewrite app_nil_r.
  - rewrite IH. now rewrite <- app_assoc.
Qed.

Lemma karr_values_elements : forall A (tr : ptrie A),
  karr_values tr = map snd (PTrieCode.elements tr).
Proof.
  intros A tr.
  pose proof (PTrieT.F9_fold_values A (list A)
    (fun acc a => acc ++ [a]) tr []) as Hfold.
  rewrite karr_fold_values_append, karr_fold_left_values in Hfold.
  exact Hfold.
Qed.

Lemma karr_nodup_map_filter : forall A B (f : A -> B) test xs,
  NoDup (map f xs) -> NoDup (map f (filter test xs)).
Proof.
  intros A B f test xs. induction xs as [|a xs IH]; intro Hunique.
  - constructor.
  - inversion Hunique as [|b bs Hnot Htail]; subst b bs.
    cbn [filter]. destruct (test a) eqn:Htest; cbn [map].
    + constructor; [|now apply IH].
      intro Hin. apply Hnot. apply in_map_iff in Hin as [p [Heq Hin]].
      apply filter_In in Hin as [Hin _]. apply in_map_iff. exists p. auto.
    + now apply IH.
Qed.


(** A dense target defect is scaled by its recorded target coefficient. *)
Definition karr_scaled_defect (qs : list Q) (target r : karr_row) : Prop :=
  (karr_eval qs (kcoeff r) - inject_Z (kright r) ==
    inject_Z (kscale r) *
      (karr_eval qs (kcoeff target) - inject_Z (kright target)))%Q.

(** One guarded reduction preserves the scaled defect under a satisfied basis row. *)
Lemma karr_reduce_scaled_defect : forall qs target d a b p r,
  length (kcoeff r) = length (kcoeff p) ->
  karr_models qs p -> kscale p = 0%Z -> karr_scaled_defect qs target r ->
  karr_scaled_defect qs target (karr_reduce d a b p r).
Proof.
  intros qs target d a b p r Hwidth Hp Hpscale Hr. unfold karr_reduce.
  set (raw := KRow (karr_cross a b (kcoeff r) (kcoeff p))
    (a * kright r - b * kright p)%Z
    (karr_cross a b (kweight r) (kweight p)) (a * kscale r - b * kscale p)%Z).
  destruct (karr_divide_factor d raw) as [factor [Hfactor Hmultiple]].
  pose proof (karr_multiple_eval factor _ _ qs Hmultiple) as Hdefect.
  destruct Hmultiple as [_ [_ [_ Hscale]]].
  change (factor * kscale (karr_divide d raw) =
    a * kscale r - b * kscale p)%Z in Hscale.
  change (inject_Z factor * (karr_eval qs (kcoeff (karr_divide d raw)) -
    inject_Z (kright (karr_divide d raw))) ==
    karr_eval qs (karr_cross a b (kcoeff r) (kcoeff p)) -
      inject_Z (a * kright r - b * kright p))%Q in Hdefect.
  setoid_rewrite (karr_eval_cross qs a b _ _ Hwidth) in Hdefect.
  unfold Z.sub in Hdefect. rewrite inject_Z_plus, inject_Z_opp, !inject_Z_mult in Hdefect.
  unfold karr_models in Hp. unfold karr_scaled_defect in *.
  setoid_rewrite Hp in Hdefect.
  assert (HscaleQ : (inject_Z factor * inject_Z (kscale (karr_divide d raw)) ==
    inject_Z a * inject_Z (kscale r))%Q).
  { rewrite <- !inject_Z_mult. apply (proj2 (inject_Z_injective _ _)).
    rewrite Hscale, Hpscale. ring. }
  apply (proj1 (Qmult_inj_l _ _ (inject_Z factor) (karr_inject_nonzero _ Hfactor))).
  eapply Qeq_trans; [exact Hdefect|].
  eapply Qeq_trans with (y := (inject_Z a *
    (karr_eval qs (kcoeff r) - inject_Z (kright r)))%Q); [ring|].
  setoid_rewrite Hr.
  eapply Qeq_trans with (y := ((inject_Z a * inject_Z (kscale r)) *
    (karr_eval qs (kcoeff target) - inject_Z (kright target)))%Q); [ring|].
  setoid_rewrite <- HscaleQ. ring.
Qed.

(** Following satisfied zero-scale basis rows preserves the target's defect exactly. *)
Lemma karr_target_scaled_defect : forall rs qs target n,
  Forall (karr_models qs) rs -> Forall (fun p => kscale p = 0%Z) rs ->
  Forall (fun p => length (kcoeff p) = n) rs ->
  forall previous r, length (kcoeff r) = n -> karr_scaled_defect qs target r ->
  karr_scaled_defect qs target (karr_target rs previous r).
Proof.
  intro rs. induction rs as [|p rs IH];
    intros qs target n Hmodels Hscales Hwidth previous r Hr Hdefect; [exact Hdefect|].
  inversion Hmodels as [|p' rs' Hp Hmodels']; subst p' rs'.
  inversion Hscales as [|p' rs' Hpscale Hscales']; subst p' rs'.
  inversion Hwidth as [|p' rs' Hpwidth Hwidth']; subst p' rs'.
  cbn [karr_target]. destruct (karr_first (kcoeff p)) as [[i a]|].
  - apply (IH qs target n Hmodels' Hscales' Hwidth').
    + rewrite karr_reduce_width; [exact Hr|now rewrite Hr, Hpwidth].
    + apply karr_reduce_scaled_defect; try assumption. now rewrite Hr, Hpwidth.
  - now apply (IH qs target n Hmodels' Hscales' Hwidth').
Qed.

(** All-zero coefficients evaluate to zero in every finite rational store. *)
Lemma karr_eval_zero : forall zs, forallb (Z.eqb 0) zs = true ->
  forall qs, (karr_eval qs zs == 0)%Q.
Proof.
  intro zs. induction zs as [|z zs IH]; intros Hzero [|q qs]; try reflexivity.
  cbn [forallb] in Hzero. apply andb_true_iff in Hzero as [Hz Htail].
  apply Z.eqb_eq in Hz. subst z.
  change (0 * q + karr_eval qs zs == 0)%Q. setoid_rewrite (IH Htail qs). ring.
Qed.

(** A modeled all-zero row cannot have a nonzero right-hand side. *)
Lemma karr_zero_model_right : forall qs r, karr_models qs r ->
  karr_zero r = true -> kright r = 0%Z.
Proof.
  intros qs r Hmodel Hzero. unfold karr_models in Hmodel.
  setoid_rewrite (karr_eval_zero _ Hzero qs) in Hmodel.
  apply (proj1 (inject_Z_injective _ _)). symmetry. exact Hmodel.
Qed.

Module KarrCode (X : KEY_OPS) (L : LANG_OPS) (F : LINEARIZE_OPS X L)
    (C : LINCERT_OPS X) <: KARR_OPS X L F C.
  Definition t := reach (list (lcons X.t)).
  Definition wparam := nat.

  Definition add_term (m : ptrie (X.t * Z)) (p : X.t * Z) : ptrie (X.t * Z) :=
    let key := X.encode (fst p) in
    match PTrieCode.get key m with
    | None => PTrieCode.set key p m
    | Some q => PTrieCode.set key (fst q, (snd q + snd p)%Z) m
    end.

  Definition normalize_coef (xs : list (X.t * Z)) : list (X.t * Z) :=
    filter (fun p => negb (Z.eqb (snd p) 0))
      (karr_values (fold_left add_term xs PTrieCode.empty)).

  Definition normalize_row (r : lcons X.t) : lcons X.t :=
    LCons _ (normalize_coef (lhs r)) (lrel r) (rhs r).

  Definition coefficient (x : X.t) (xs : list (X.t * Z)) : Z :=
    fold_right (fun p z => if X.eqb x (fst p) then (snd p + z)%Z else z) 0%Z xs.

  Definition variables (P : list (lcons X.t)) : list X.t :=
    map fst (karr_values
      (fold_left add_term (flat_map lhs P) PTrieCode.empty)).

  Definition dense (xs : list X.t) (r : lcons X.t) : list Z :=
    map (fun x => coefficient x (lhs r)) xs.

  Definition sparse (xs : list X.t) (zs : list Z) : list (X.t * Z) :=
    filter (fun p => negb (Z.eqb (snd p) 0)) (List.combine xs zs).

  Fixpoint seed_rows (xs : list X.t) (total index : nat) (P : list (lcons X.t))
      : list karr_row :=
    match P with
    | [] => []
    | r :: P =>
      let rest := seed_rows xs total (S index) P in
      match lrel r with
      | REq => KRow (dense xs r) (rhs r) (karr_unit total index) 0%Z :: rest
      | RLe => rest
      end
    end.

  Definition equality_basis (xs : list X.t) (P : list (lcons X.t)) : list karr_row :=
    karr_bareiss (length xs) 1 (seed_rows xs (length P) 0 (map normalize_row P)).

  Fixpoint empty_certificate (P : list (lcons X.t)) (rs : list karr_row)
      : option (list Z) :=
    match rs with
    | [] => None
    | r :: rs =>
      if karr_zero r && negb (Z.eqb (kright r) 0) && C.check_empty P (kweight r)
      then Some (kweight r) else empty_certificate P rs
    end.

  Definition contradiction (P : list (lcons X.t)) : option (list Z) :=
    empty_certificate P (equality_basis (variables P) P).

  Definition row_eqb (r s : lcons X.t) : bool :=
    let relation := match lrel r, lrel s with
      | REq, REq | RLe, RLe => true
      | _, _ => false
      end in
    relation && Z.eqb (rhs r) (rhs s) &&
      karr_list_eqb (fun p q => X.eqb (fst p) (fst q) && Z.eqb (snd p) (snd q))
        (lhs r) (lhs s).

  Definition target_certificate (P : list (lcons X.t)) (c : lcons X.t) : option cert :=
    let xs := variables (c :: P) in
    let r := karr_target (equality_basis xs P) 1
      (KRow (dense xs c) (rhs c) (repeat 0%Z (length P)) 1) in
    let sign := if (kscale r <? 0)%Z then (-1)%Z else 1%Z in
    let right := match lrel c with
      | REq => Z.eqb (kright r) 0
      | RLe => (0 <=? sign * kright r)%Z
      end in
    if karr_zero r && negb (Z.eqb (kscale r) 0) && right then
      Some (Cert (map (fun z => (- sign * z)%Z) (kweight r)) (Z.abs (kscale r)) false)
    else None.

  Definition entail_cert (P : list (lcons X.t)) (c : lcons X.t) : option cert :=
    let candidate := match contradiction P with
      | Some ms => Some (Cert ms 1 false)
      | None => target_certificate P c
      end in
    match candidate with
    | Some k => if C.check_entails P c k then Some k else None
    | None => None
    end.

  Definition entails (P : list (lcons X.t)) (r : lcons X.t) : bool :=
    existsb (row_eqb r) P ||
      match entail_cert P r with Some _ => true | None => false end.

  Definition leb (a b : t) : bool :=
    match a, b with
    | Unreached, _ => true
    | Reached P, Unreached =>
      match contradiction P with Some _ => true | None => false end
    | Reached P, Reached Q =>
      match contradiction P with
      | Some _ => true
      | None => forallb (entails P) Q
      end
    end.

  Definition bot : t := Unreached.

  Definition is_bot (s : t) : bool :=
    match s with
    | Unreached => true
    | Reached P => match contradiction P with Some _ => true | None => false end
    end.

  Fixpoint hull_left (xs : list X.t) (total index : nat) (P : list (lcons X.t))
      : list karr_row :=
    match P with
    | [] => []
    | r :: P =>
      let rest := hull_left xs total (S index) P in
      match lrel r with
      | REq =>
        KRow (dense xs r ++ (- rhs r)%Z :: repeat 0%Z (S (length xs)))
          0 (karr_unit total index) 0 :: rest
      | RLe => rest
      end
    end.

  Fixpoint hull_right (xs : list X.t) (total index : nat) (P : list (lcons X.t))
      : list karr_row :=
    match P with
    | [] => []
    | r :: P =>
      let rest := hull_right xs total (S index) P in
      match lrel r with
      | REq =>
        let zs := dense xs r in
        KRow (map Z.opp zs ++ rhs r :: zs ++ [rhs r])
          0 (karr_unit total index) 0 :: rest
      | RLe => rest
      end
    end.

  Definition checked_hull_row (xs : list X.t) (a b : list (lcons X.t)) (r : karr_row)
      : option (lcons X.t) :=
    let aux := S (length xs) in
    let zs := skipn aux (kcoeff r) in
    let c := LCons _ (sparse xs zs) REq (karr_nth (length xs) zs) in
    if forallb (Z.eqb 0) (firstn aux (kcoeff r)) && negb (forallb (Z.eqb 0) zs) &&
      C.check_entails a c (Cert (firstn (length a) (kweight r)) 1 false) &&
      C.check_entails b c (Cert (skipn (length a) (kweight r)) 1 false)
    then Some c else None.

  Definition present {A} (xs : list (option A)) : list A :=
    flat_map (fun o => match o with Some x => [x] | None => [] end) xs.

  Definition affine_hull (a b : list (lcons X.t)) : list (lcons X.t) :=
    let P := map normalize_row a in
    let Q := map normalize_row b in
    let xs := variables (P ++ Q) in
    let total := length a + length b in
    let rows := hull_left xs total 0 P ++ hull_right xs total (length a) Q in
    let basis := karr_bareiss (2 * length xs + 2) 1 rows in
    present (map (checked_hull_row xs a b) basis).

  Definition join (a b : t) : t :=
    match a, b with
    | Unreached, s | s, Unreached => s
    | Reached P, Reached Q => Reached (affine_hull P Q)
    end.

  Definition top : t := Reached nil.

  Definition meet (a b : t) : t :=
    match a, b with
    | Reached P, Reached Q => Reached (map normalize_row (P ++ Q))
    | _, _ => Unreached
    end.

  Definition widen (_ : wparam) (a b : t) : t := if leb b a then a else join a b.

  Definition narrow (_ : t) (b : t) : t := b.

  Definition subst (x : X.t) (f : lin X.t) (r : lcons X.t) : lcons X.t :=
    normalize_row (LCons _
      (flat_map (fun p => if X.eqb (fst p) x
        then map (fun q => (fst q, (snd p * snd q)%Z)) (coef f) else [p]) (lhs r))
      (lrel r) (rhs r - coefficient x (lhs r) * cst f)%Z).

  Definition mentions (x : X.t) (r : lcons X.t) : bool :=
    negb (Z.eqb (coefficient x (lhs r)) 0).

  Definition projected_row (x : X.t) (xs : list X.t) (P : list (lcons X.t))
      (r : karr_row) : option (lcons X.t) :=
    let c := LCons _ (sparse xs (kcoeff r)) REq (kright r) in
    if negb (mentions x c) && C.check_entails P c (Cert (kweight r) 1 false)
    then Some c else None.

  Definition project (x : X.t) (P : list (lcons X.t)) : list (lcons X.t) :=
    let xs := x :: filter (fun y => negb (X.eqb y x)) (variables P) in
    let rows := karr_bareiss 1 1 (seed_rows xs (length P) 0 (map normalize_row P)) in
    present (map (projected_row x xs P) rows) ++
      filter (fun r => match lrel r with
        | REq => false | RLe => negb (mentions x r) end) (map normalize_row P).

  Definition havoc (x : X.t) (s : t) : t :=
    match s with
    | Unreached => Unreached
    | Reached P => Reached (project x P)
    end.

  Definition inverse_row (x : X.t) (f : lin X.t) (a : Z) (r : lcons X.t)
      : lcons X.t :=
    let b := coefficient x (lhs r) in
    let sign := if (a <? 0)%Z then (-1)%Z else 1%Z in
    let without := filter (fun p => negb (X.eqb (fst p) x)) in
    normalize_row (LCons _
      ((x, (sign * b)%Z) ::
       map (fun p => (fst p, (Z.abs a * snd p)%Z)) (without (lhs r)) ++
       map (fun p => (fst p, (- sign * b * snd p)%Z)) (without (coef f)))
      (lrel r) (Z.abs a * rhs r + sign * b * cst f)%Z).

  Definition assign_rows (x : X.t) (f : lin X.t) (P : list (lcons X.t))
      : list (lcons X.t) :=
    let a := coefficient x (coef f) in
    if Z.eqb a 0 then
      normalize_row (LCons _ ((x, 1%Z) :: map (fun p => (fst p, (- snd p)%Z)) (coef f))
        REq (cst f)) :: project x P
    else map (inverse_row x f a) (map normalize_row P).

  Definition assign (x : X.t) (e : term L.op X.t) (s : t) : t :=
    match s with
    | Unreached => Unreached
    | Reached P =>
      match F.lin_of e with
      | Some (f, NoWrap) => Reached (assign_rows x f P)
      | _ => havoc x s
      end
    end.

  Definition atom_rows (a : atom X.t) : list (lcons X.t) :=
    match alw a, arw a, acmp a with
    | NoWrap, NoWrap, CEq =>
      [normalize_row (LCons _
        (coef (al a) ++ map (fun p => (fst p, (- snd p)%Z)) (coef (ar a)))
        REq (cst (ar a) - cst (al a))%Z)]
    | _, _, _ => []
    end.

  Definition assume (g : L.guard) (es : list (term L.op X.t)) (s : t) : t :=
    match s with
    | Unreached => Unreached
    | Reached P => Reached (flat_map atom_rows (F.atoms_of g es) ++ map normalize_row P)
    end.

  Definition range (e : term L.op X.t) (s : t) : bnd * bnd :=
    match s, F.lin_of e with
    | Reached P, Some (f, NoWrap) =>
      let xs := variables (LCons _ (coef f) REq 0 :: P) in
      let r := karr_target (equality_basis xs P) 1
        (KRow (map (fun x => coefficient x (coef f)) xs) 0 (repeat 0%Z (length P)) 1) in
      let z := (- kright r / kscale r + cst f)%Z in
      match entail_cert P (LCons _ (coef f) REq (z - cst f)%Z) with
      | Some _ => (Fin z, Fin z)
      | None => (NegInf, PosInf)
      end
    | _, _ => (NegInf, PosInf)
    end.
End KarrCode.

Module Karr (X : KEY) (L : LANG) (N : NUM_VIEW L)
    (F : LINEARIZE X L N) (C : LINCERT X) <: KARR X L N F C.
  Include KarrCode X L F C.
   Definition wrank (_ : wparam) (s : t) : nat :=
    match s with Unreached => 0 | Reached P => length P end.
  Definition ngamma (s : t) (v : X.t -> Z) : Prop :=
    match s with Unreached => False | Reached P => Forall (sat v) P end.

  (** A key is equal to itself in the executable test. *)
  Lemma key_eqb_refl : forall x, X.eqb x x = true.
  Proof.
    intro x. destruct (X.eqb_spec x x); [reflexivity | contradiction].
  Qed.

  (** Successful key comparison gives propositional equality. *)
  Lemma key_eqb_eq : forall x y, X.eqb x y = true -> x = y.
  Proof.
    intros x y Hsame. destruct (X.eqb_spec x y); congruence.
  Qed.

  (** Comparing keys is symmetric. *)
  Lemma key_eqb_sym : forall x y, X.eqb x y = X.eqb y x.
  Proof.
    intros x y. destruct (X.eqb_spec x y), (X.eqb_spec y x); congruence.
  Qed.

  (** Every coefficient list passes its own literal comparison. *)
  Lemma coefficient_list_eqb_refl : forall xs,
    karr_list_eqb (fun p q => X.eqb (fst p) (fst q) && Z.eqb (snd p) (snd q)) xs xs = true.
  Proof.
    induction xs as [| [x a] xs IH]; [reflexivity |].
    cbn [karr_list_eqb fst snd]. rewrite key_eqb_refl, Z.eqb_refl, IH. reflexivity.
  Qed.

  (** Literal coefficient comparison retains order and multiplicity. *)
  Lemma coefficient_list_eqb_sound : forall xs ys,
    karr_list_eqb (fun p q => X.eqb (fst p) (fst q) && Z.eqb (snd p) (snd q)) xs ys = true ->
    xs = ys.
  Proof.
    induction xs as [| [x a] xs IH]; intros [| [y b] ys] Hsame;
      cbn [karr_list_eqb fst snd] in Hsame; try discriminate; [reflexivity |].
    apply andb_true_iff in Hsame as [Hhead Htail].
    apply andb_true_iff in Hhead as [Hkey Hcoeff].
    apply key_eqb_eq in Hkey. apply Z.eqb_eq in Hcoeff.
    subst y b. f_equal. now apply IH.
  Qed.

  (** A row is literally equal to itself. *)
  Lemma row_eqb_refl : forall r, row_eqb r r = true.
  Proof.
    intros [xs rel z]. unfold row_eqb. cbn [lhs lrel rhs].
    rewrite Z.eqb_refl, coefficient_list_eqb_refl. destruct rel; reflexivity.
  Qed.

  (** Literal row comparison decides equality of the complete stored row. *)
  Lemma row_eqb_sound : forall r s, row_eqb r s = true -> r = s.
  Proof.
    intros [xs rel z] [ys rel' w] Hsame. unfold row_eqb in Hsame.
    cbn [lhs lrel rhs] in Hsame. destruct rel, rel'; cbn in Hsame; try discriminate;
      apply andb_true_iff in Hsame as [Hright Hleft];
      apply Z.eqb_eq in Hright; apply coefficient_list_eqb_sound in Hleft;
      now subst.
  Qed.

  (** The producer returns only certificates that its checker accepted. *)
  Lemma entail_cert_checked : forall P c k,
    entail_cert P c = Some k -> C.check_entails P c k = true.
  Proof.
    intros P c k Hcert. unfold entail_cert in Hcert.
    remember (match contradiction P with
      | Some ms => Some (Cert ms 1 false)
      | None => target_certificate P c
      end) as candidate.
    destruct candidate as [produced |]; [| discriminate].
    destruct (C.check_entails P c produced) eqn:Hcheck; [| discriminate].
    injection Hcert as Hsame. subst k. exact Hcheck.
  Qed.

  (** Every returned contradiction passed the contradiction checker. *)
  Lemma empty_certificate_checked : forall P rs ms,
    empty_certificate P rs = Some ms -> C.check_empty P ms = true.
  Proof.
    intros P rs. induction rs as [| r rs IH]; intros ms Hcert; [discriminate |].
    cbn [empty_certificate] in Hcert.
    destruct (karr_zero r && negb (Z.eqb (kright r) 0) && C.check_empty P (kweight r))
      eqn:Hcheck.
    - injection Hcert as Hsame. subst ms.
      now apply andb_true_iff in Hcheck as [_ Hcheck].
    - now apply IH.
  Qed.

  (** Left-system infeasibility is always checked against the raw input. *)
  Lemma contradiction_checked : forall P ms,
    contradiction P = Some ms -> C.check_empty P ms = true.
  Proof.
    intros P ms Hcert. unfold contradiction in Hcert.
    now apply empty_certificate_checked in Hcert.
  Qed.

  (** Both branches of row inclusion retain every integer model. *)
  Lemma entails_sound : forall P r v, entails P r = true -> Forall (sat v) P -> sat v r.
  Proof.
    intros P r v Hcheck Hmodels. unfold entails in Hcheck.
    apply orb_true_iff in Hcheck as [Hliteral | Hcert].
    - apply existsb_exists in Hliteral as [s [Hin Hsame]].
      apply row_eqb_sound in Hsame. subst s.
      now apply (proj1 (Forall_forall _ _) Hmodels).
    - destruct (entail_cert P r) as [k |] eqn:Hproduced; [| discriminate].
      eapply (C.check_entails_sound P r k).
      + exact (entail_cert_checked P r k Hproduced).
      + exact Hmodels.
  Qed.

  (** Every returned contradiction excludes each integer model of its input. *)
  Lemma contradiction_sound : forall P ms v,
    contradiction P = Some ms -> ~ Forall (sat v) P.
  Proof.
    intros P ms v Hcert. apply C.check_empty_sound with (ms := ms).
    now apply contradiction_checked in Hcert.
  Qed.

  Definition normalization_wf (m : ptrie (X.t * Z)) : Prop :=
    forall p q, PTrieCode.get p m = Some q -> X.encode (fst q) = p.

  Lemma normalization_empty : normalization_wf PTrieCode.empty.
  Proof.
    intros p q Hget. rewrite PTrie.get_empty in Hget. discriminate.
  Qed.

  Lemma add_term_wf : forall m p, normalization_wf m -> normalization_wf (add_term m p).
  Proof.
    intros m p Hwf. unfold add_term.
    destruct (PTrieCode.get (X.encode (fst p)) m) as [q|] eqn:Hq;
      intros key value Hvalue;
      destruct (Pos.eq_dec key (X.encode (fst p))) as [Heq|Hneq].
    - subst key. rewrite PTrie.get_set_same in Hvalue. inversion Hvalue; subst value.
      cbn [fst]. exact (Hwf _ _ Hq).
    - rewrite PTrie.get_set_other in Hvalue by exact Hneq. exact (Hwf _ _ Hvalue).
    - subst key. rewrite PTrie.get_set_same in Hvalue. inversion Hvalue; reflexivity.
    - rewrite PTrie.get_set_other in Hvalue by exact Hneq. exact (Hwf _ _ Hvalue).
  Qed.

  Lemma normalize_fold_wf : forall xs m,
    normalization_wf m -> normalization_wf (fold_left add_term xs m).
  Proof.
    intro xs. induction xs as [|p xs IH]; intros m Hwf; cbn [fold_left].
    - exact Hwf.
    - apply IH. now apply add_term_wf.
  Qed.

  Lemma add_term_mass : forall (v : X.t -> Z) m p, normalization_wf m ->
    karr_zmass (fun q => (snd q * v (fst q))%Z) (add_term m p) =
    (karr_zmass (fun q => (snd q * v (fst q))%Z) m + snd p * v (fst p))%Z.
  Proof.
    intros v m p Hwf. unfold add_term.
    destruct (PTrieCode.get (X.encode (fst p)) m) as [q|] eqn:Hq;
      rewrite karr_zmass_set, Hq; cbn [karr_zoption fst snd].
    - assert (Hkey : fst q = fst p).
      { apply X.encode_inj. exact (Hwf _ _ Hq). }
      rewrite Hkey. ring.
    - ring.
  Qed.

  Lemma normalize_fold_mass : forall (v : X.t -> Z) xs m, normalization_wf m ->
    karr_zmass (fun q => (snd q * v (fst q))%Z) (fold_left add_term xs m) =
    (karr_zmass (fun q => (snd q * v (fst q))%Z) m + eval_coef v xs)%Z.
  Proof.
    intros v xs. induction xs as [|p xs IH]; intros m Hwf; cbn [fold_left].
    - unfold eval_coef. cbn [fold_right]. ring.
    - rewrite (IH _ (add_term_wf _ _ Hwf)), (add_term_mass v m p Hwf).
      unfold eval_coef. cbn [fold_right]. ring.
  Qed.

  Lemma eval_coef_nonzero : forall (v : X.t -> Z) xs,
    eval_coef v (filter (fun p => negb (Z.eqb (snd p) 0)) xs) = eval_coef v xs.
  Proof.
    intros v xs. unfold eval_coef.
    induction xs as [|[x z] xs IH]; cbn [filter fold_right snd fst].
    - reflexivity.
    - destruct (Z.eqb z 0) eqn:Hz; cbn [negb fold_right fst snd].
      + apply Z.eqb_eq in Hz. subst z. rewrite IH. ring.
      + rewrite IH. reflexivity.
  Qed.

  Lemma normalize_coef_eval : forall (v : X.t -> Z) xs,
    eval_coef v (normalize_coef xs) = eval_coef v xs.
  Proof.
    intros v xs. unfold normalize_coef. rewrite eval_coef_nonzero.
    change (karr_zmass (fun q => (snd q * v (fst q))%Z)
      (fold_left add_term xs PTrieCode.empty) = eval_coef v xs).
    rewrite (normalize_fold_mass v xs PTrieCode.empty normalization_empty).
    reflexivity.
  Qed.

  Lemma normalization_values_nodup : forall m, normalization_wf m ->
    NoDup (map fst (karr_values m)).
  Proof.
    intros m Hwf. apply NoDup_map_inv with (f := X.encode).
    rewrite karr_values_elements, !map_map.
    assert (Hkeys : map (fun p => X.encode (fst (snd p))) (PTrieCode.elements m) =
      map fst (PTrieCode.elements m)).
    { apply map_ext_in. intros [key p] Hin. cbn [fst snd].
      apply Hwf. apply (proj1 (PTrie.elements_spec _ m key p)). exact Hin. }
    rewrite Hkeys. apply PTrie.elements_nodup.
  Qed.

  Lemma normalize_coef_nodup : forall xs, NoDup (map fst (normalize_coef xs)).
  Proof.
    intro xs. unfold normalize_coef. apply karr_nodup_map_filter.
    apply normalization_values_nodup. apply normalize_fold_wf. apply normalization_empty.
  Qed.

  Lemma coefficient_as_eval : forall x xs,
    coefficient x xs = eval_coef (fun y => if X.eqb x y then 1%Z else 0%Z) xs.
  Proof.
    intros x xs. unfold coefficient, eval_coef.
    induction xs as [|[y z] xs IH]; cbn [fold_right fst snd].
    - reflexivity.
    - destruct (X.eqb x y); rewrite IH; ring.
  Qed.

  Lemma normalize_coef_coefficient : forall x xs,
    coefficient x (normalize_coef xs) = coefficient x xs.
  Proof.
    intros x xs. rewrite !coefficient_as_eval. apply normalize_coef_eval.
  Qed.

  Lemma add_term_mass_Q : forall (v : X.t -> Q) m p, normalization_wf m ->
    (karr_qmass (fun q => inject_Z (snd q) * v (fst q)) (add_term m p) ==
    karr_qmass (fun q => inject_Z (snd q) * v (fst q)) m +
      inject_Z (snd p) * v (fst p))%Q.
  Proof.
    intros v m p Hwf. unfold add_term.
    destruct (PTrieCode.get (X.encode (fst p)) m) as [q|] eqn:Hq;
      setoid_rewrite karr_qmass_set; rewrite Hq; cbn [karr_qoption fst snd].
    - assert (Hkey : fst q = fst p).
      { apply X.encode_inj. exact (Hwf _ _ Hq). }
      rewrite Hkey, inject_Z_plus. ring.
    - ring.
  Qed.

  Lemma normalize_fold_mass_Q : forall (v : X.t -> Q) xs m, normalization_wf m ->
    (karr_qmass (fun q => inject_Z (snd q) * v (fst q)) (fold_left add_term xs m) ==
    karr_qmass (fun q => inject_Z (snd q) * v (fst q)) m + karr_eval_coef_Q v xs)%Q.
  Proof.
    intros v xs. induction xs as [|p xs IH]; intros m Hwf; cbn [fold_left].
    - change (karr_qmass (fun q => inject_Z (snd q) * v (fst q)) m ==
        karr_qmass (fun q => inject_Z (snd q) * v (fst q)) m + 0)%Q. ring.
    - setoid_rewrite (IH _ (add_term_wf _ _ Hwf)).
      setoid_rewrite (add_term_mass_Q v m p Hwf).
      change (karr_qmass (fun q => inject_Z (snd q) * v (fst q)) m +
        inject_Z (snd p) * v (fst p) + karr_eval_coef_Q v xs ==
        karr_qmass (fun q => inject_Z (snd q) * v (fst q)) m +
        (inject_Z (snd p) * v (fst p) + karr_eval_coef_Q v xs))%Q. ring.
  Qed.

  Lemma eval_coef_nonzero_Q : forall (v : X.t -> Q) xs,
    (karr_eval_coef_Q v (filter (fun p => negb (Z.eqb (snd p) 0)) xs) ==
      karr_eval_coef_Q v xs)%Q.
  Proof.
    intros v xs. induction xs as [|[x z] xs IH].
    - reflexivity.
    - cbn [filter snd]. destruct (Z.eqb z 0) eqn:Hz; cbn [negb].
      + apply Z.eqb_eq in Hz. subst z.
        change (karr_eval_coef_Q v (filter (fun p => negb (Z.eqb (snd p) 0)) xs) ==
          0 * v x + karr_eval_coef_Q v xs)%Q.
        setoid_rewrite IH. ring.
      + change (inject_Z z * v x +
          karr_eval_coef_Q v (filter (fun p => negb (Z.eqb (snd p) 0)) xs) ==
          inject_Z z * v x + karr_eval_coef_Q v xs)%Q.
        now setoid_rewrite IH.
  Qed.

  Lemma normalize_coef_eval_Q : forall (v : X.t -> Q) xs,
    (karr_eval_coef_Q v (normalize_coef xs) == karr_eval_coef_Q v xs)%Q.
  Proof.
    intros v xs. unfold normalize_coef. setoid_rewrite eval_coef_nonzero_Q.
    change (karr_qmass (fun q => inject_Z (snd q) * v (fst q))
      (fold_left add_term xs PTrieCode.empty) == karr_eval_coef_Q v xs)%Q.
    setoid_rewrite (normalize_fold_mass_Q v xs PTrieCode.empty normalization_empty).
    change (0 + karr_eval_coef_Q v xs == karr_eval_coef_Q v xs)%Q. ring.
  Qed.

  (** Coefficient evaluation respects concatenation. *)
  Lemma eval_coef_app : forall (v : X.t -> Z) xs ys,
    eval_coef v (xs ++ ys) = (eval_coef v xs + eval_coef v ys)%Z.
  Proof.
    intros v xs. unfold eval_coef. induction xs as [| [x a] xs IH]; intro ys;
      cbn [fold_right fst snd app]; [reflexivity |].
    rewrite IH. ring.
  Qed.

  (** Scaling each stored coefficient scales its evaluation. *)
  Lemma eval_coef_scale : forall (v : X.t -> Z) a xs,
    eval_coef v (map (fun p => (fst p, (a * snd p)%Z)) xs) =
      (a * eval_coef v xs)%Z.
  Proof.
    intros v a xs. unfold eval_coef. induction xs as [| [x b] xs IH];
      cbn [fold_right map fst snd]; [ring |].
    rewrite IH. ring.
  Qed.

  (** Negating stored coefficients negates their evaluation. *)
  Lemma eval_coef_opp : forall (v : X.t -> Z) xs,
    eval_coef v (map (fun p => (fst p, (- snd p)%Z)) xs) = (- eval_coef v xs)%Z.
  Proof.
    intros v xs. unfold eval_coef. induction xs as [| [x a] xs IH];
      cbn [fold_right map fst snd]; [ring |].
    rewrite IH. ring.
  Qed.

  (** A concrete update changes a linear form by its total coefficient at the key. *)
  Lemma eval_coef_update : forall (v : X.t -> Z) x z xs,
    eval_coef (upd X.eqb v x z) xs =
      (eval_coef v xs + coefficient x xs * (z - v x))%Z.
  Proof.
    intros v x z xs. unfold eval_coef, coefficient.
    induction xs as [| [y a] xs IH]; [reflexivity |].
    cbn [fold_right fst snd]. rewrite IH. unfold upd.
    destruct (X.eqb_spec y x) as [Hsame | Hother].
    - subst y. rewrite key_eqb_refl. ring.
    - assert (Hreverse : X.eqb x y = false).
      { destruct (X.eqb_spec x y); congruence. }
      rewrite Hreverse. ring.
  Qed.

  (** Pointwise equal stores give equal coefficient evaluations. *)
  Lemma eval_coef_pointwise : forall (v w : X.t -> Z) xs,
    (forall x, v x = w x) -> eval_coef v xs = eval_coef w xs.
  Proof.
    intros v w xs Hsame. unfold eval_coef.
    induction xs as [| [x a] xs IH]; [reflexivity |].
    cbn [fold_right fst snd]. now rewrite Hsame, IH.
  Qed.

  (** Satisfaction depends only on the numeric values read from a store. *)
  Lemma sat_pointwise : forall (v w : X.t -> Z) r,
    (forall x, v x = w x) -> sat v r -> sat w r.
  Proof.
    intros v w r Hsame Hsat. unfold sat in *.
    rewrite <- (eval_coef_pointwise v w (lhs r) Hsame). exact Hsat.
  Qed.

  (** Row normalization keeps the denoted constraint. *)
  Lemma normalize_row_sat : forall v r, sat v (normalize_row r) <-> sat v r.
  Proof.
    intros v r. unfold sat, normalize_row. cbn [lrel lhs rhs].
    rewrite normalize_coef_eval. reflexivity.
  Qed.

  (** Zero total coefficient makes a row independent of the updated key. *)
  Lemma unmentioned_sat : forall v x z r,
    mentions x r = false -> sat v r -> sat (upd X.eqb v x z) r.
  Proof.
    intros v x z r Hfree Hsat. unfold mentions in Hfree.
    apply negb_false_iff in Hfree. apply Z.eqb_eq in Hfree.
    unfold sat in *. rewrite eval_coef_update, Hfree.
    destruct (lrel r); cbn in *; lia.
  Qed.

  (** Collecting successful optional results preserves their proved predicate. *)
  Lemma present_forall : forall A B (f : A -> option B) (R : B -> Prop) xs,
    (forall x r, f x = Some r -> R r) -> Forall R (present (map f xs)).
  Proof.
    intros A B f R xs Hresult. induction xs as [| x xs IH]; [constructor |].
    cbn [present map flat_map]. destruct (f x) as [r |] eqn:Hsome.
    - constructor; [now apply Hresult with (x := x) | exact IH].
    - exact IH.
  Qed.

  (** Checked projection rows retain every replacement of the eliminated variable. *)
  Lemma projected_row_sound : forall x xs P r c v z,
    projected_row x xs P r = Some c -> Forall (sat v) P ->
    sat (upd X.eqb v x z) c.
  Proof.
    intros x xs P r c v z Hrow Hmodels. unfold projected_row in Hrow.
    remember (LCons X.t (sparse xs (kcoeff r)) REq (kright r)) as candidate.
    destruct (negb (mentions x candidate) &&
      C.check_entails P candidate (Cert (kweight r) 1 false)) eqn:Hcheck;
      [| discriminate].
    injection Hrow as Hsame. subst c.
    apply andb_true_iff in Hcheck as [Hfree Hchecked].
    apply negb_true_iff in Hfree. apply unmentioned_sat; [exact Hfree |].
    eapply C.check_entails_sound; [exact Hchecked | exact Hmodels].
  Qed.

  (** Projection keeps every state obtained by assigning an arbitrary new value. *)
  Lemma project_sound : forall x P v z, Forall (sat v) P ->
    Forall (sat (upd X.eqb v x z)) (project x P).
  Proof.
    intros x P v z Hmodels. unfold project. apply Forall_app. split.
    - apply present_forall. intros r c Hrow.
      eapply projected_row_sound; [exact Hrow | exact Hmodels].
    - apply Forall_forall. intros r Hin. apply filter_In in Hin as [Hin Hkeep].
      apply in_map_iff in Hin as [s [Hsame Hin]]. subst r.
      apply unmentioned_sat.
      + destruct (lrel (normalize_row s)); [discriminate |].
        now apply negb_true_iff in Hkeep.
      + apply normalize_row_sat.
        now apply (proj1 (Forall_forall _ _) Hmodels).
  Qed.

  (** Substitution expands each occurrence, including repeated keys. *)
  Lemma eval_coef_subst : forall v x f xs,
    eval_coef v
      (flat_map (fun p => if X.eqb (fst p) x
        then map (fun q => (fst q, (snd p * snd q)%Z)) (coef f) else [p]) xs) =
      (eval_coef (upd X.eqb v x (eval_lin v f)) xs - coefficient x xs * cst f)%Z.
  Proof.
    intros v x f xs. induction xs as [| [y a] xs IH]; [reflexivity |].
    cbn [flat_map fst snd]. rewrite eval_coef_app, IH.
    cbn [eval_coef coefficient fold_right fst snd]. unfold upd.
    destruct (X.eqb_spec y x) as [Hsame | Hother].
    - subst y. rewrite key_eqb_refl, eval_coef_scale.
      unfold eval_lin, coefficient, eval_coef. ring.
    - assert (Hreverse : X.eqb x y = false).
      { destruct (X.eqb_spec x y); congruence. }
      rewrite Hreverse. unfold eval_coef, coefficient. cbn [fold_right fst snd]. ring.
  Qed.

  (** Removing a variable subtracts its total contribution to the form. *)
  Lemma eval_coef_without : forall v x xs,
    eval_coef v (filter (fun p => negb (X.eqb (fst p) x)) xs) =
      (eval_coef v xs - coefficient x xs * v x)%Z.
  Proof.
    intros v x xs. unfold eval_coef, coefficient.
    induction xs as [| [y a] xs IH]; [reflexivity |].
    cbn [filter fst snd fold_right].
    destruct (X.eqb_spec y x) as [Hsame | Hother].
    - subst y. rewrite key_eqb_refl. cbn [negb]. rewrite IH.
      cbn [fold_right fst snd]. ring.
    - assert (Hreverse : X.eqb x y = false).
      { destruct (X.eqb_spec x y); congruence. }
      rewrite Hreverse. cbn [negb fold_right fst snd]. rewrite IH. ring.
  Qed.

  (** The selected sign turns a nonzero coefficient into its absolute value. *)
  Lemma coefficient_sign_abs : forall a,
    ((if (a <? 0)%Z then (-1)%Z else 1%Z) * a = Z.abs a)%Z.
  Proof.
    intros [| p | p]; cbn; ring.
  Qed.

  (** Replacing x by its affine value satisfies the inverse image of each old row. *)
  Lemma inverse_row_eval : forall (v : X.t -> Z) x f a r,
    a = coefficient x (coef f) ->
    eval_coef (upd X.eqb v x (eval_lin v f)) (lhs (inverse_row x f a r)) =
      (Z.abs a * eval_coef v (lhs r) +
       (if (a <? 0)%Z then (-1)%Z else 1%Z) * coefficient x (lhs r) * cst f)%Z.
  Proof.
    intros v x f a r Ha.
    set (sign := if (a <? 0)%Z then (-1)%Z else 1%Z).
    set (b := coefficient x (lhs r)).
    unfold inverse_row. fold sign b. cbn [normalize_row lhs].
    rewrite normalize_coef_eval.
    change ((sign * b * upd X.eqb v x (eval_lin v f) x +
      eval_coef (upd X.eqb v x (eval_lin v f))
        (map (fun p => (fst p, (Z.abs a * snd p)%Z))
          (filter (fun p => negb (X.eqb (fst p) x)) (lhs r)) ++
         map (fun p => (fst p, (- sign * b * snd p)%Z))
          (filter (fun p => negb (X.eqb (fst p) x)) (coef f))))%Z =
      (Z.abs a * eval_coef v (lhs r) + sign * b * cst f)%Z).
    rewrite eval_coef_app, !eval_coef_scale, !eval_coef_without, !eval_coef_update.
    unfold upd. rewrite key_eqb_refl. rewrite <- Ha. fold b.
    pose proof (coefficient_sign_abs a) as Hsign. fold sign in Hsign.
    rewrite <- Hsign. unfold eval_lin. ring.
  Qed.

  (** Positive scaling in an inverse row preserves both equality and inequality. *)
  Lemma inverse_row_sound : forall (v : X.t -> Z) x f r,
    sat v r ->
    sat (upd X.eqb v x (eval_lin v f))
      (inverse_row x f (coefficient x (coef f)) r).
  Proof.
    intros v x f r Hsat. unfold sat.
    rewrite inverse_row_eval by reflexivity.
    cbn [inverse_row normalize_row lrel rhs].
    pose proof (Z.abs_nonneg (coefficient x (coef f))) as Hpositive.
    unfold sat in Hsat. destruct (lrel r); nia.
  Qed.

  (** An assignment independent of the old x establishes its defining equality. *)
  Lemma assignment_equation_sound : forall (v : X.t -> Z) x f,
    coefficient x (coef f) = 0%Z ->
    sat (upd X.eqb v x (eval_lin v f))
      (normalize_row (LCons X.t
        ((x, 1%Z) :: map (fun p => (fst p, (- snd p)%Z)) (coef f)) REq (cst f))).
  Proof.
    intros v x f Hfree. apply normalize_row_sat.
    change ((1 * upd X.eqb v x (eval_lin v f) x +
      eval_coef (upd X.eqb v x (eval_lin v f))
        (map (fun p => (fst p, (- snd p)%Z)) (coef f)))%Z = cst f).
    rewrite eval_coef_opp, eval_coef_update, Hfree.
    unfold upd, eval_lin. rewrite key_eqb_refl. ring.
  Qed.

  (** Both affine assignment branches retain the concrete updated store. *)
  Lemma assign_rows_sound : forall (v : X.t -> Z) x f P,
    Forall (sat v) P -> Forall (sat (upd X.eqb v x (eval_lin v f))) (assign_rows x f P).
  Proof.
    intros v x f P Hmodels. unfold assign_rows.
    destruct (Z.eqb (coefficient x (coef f)) 0) eqn:Hzero.
    - apply Z.eqb_eq in Hzero. constructor.
      + now apply assignment_equation_sound.
      + now apply project_sound.
    - apply Forall_forall. intros r Hin.
      apply in_map_iff in Hin as [s [Hsame Hin]]. subst r.
      apply inverse_row_sound. apply in_map_iff in Hin as [r [Hsame Hin]]. subst s.
      apply normalize_row_sat. now apply (proj1 (Forall_forall _ _) Hmodels).
  Qed.

  (** Numeric interpretation commutes pointwise with an update of a concrete store. *)
  Lemma numeric_update_models : forall st x c P,
    Forall (sat (upd X.eqb (fun y => N.num (st y)) x (N.num c))) P ->
    Forall (sat (fun y => N.num (upd X.eqb st x c y))) P.
  Proof.
    intros st x c P Hmodels. apply Forall_forall. intros r Hin.
    apply sat_pointwise with (v := upd X.eqb (fun y => N.num (st y)) x (N.num c)).
    - intro y. unfold upd. destruct (X.eqb y x); reflexivity.
    - now apply (proj1 (Forall_forall _ _) Hmodels).
  Qed.

  (** Every key already present in the accumulator survives another insertion. *)
  Lemma add_term_present : forall key m p,
    key = X.encode (fst p) \/ (exists q, PTrieCode.get key m = Some q) ->
    exists q, PTrieCode.get key (add_term m p) = Some q.
  Proof.
    intros key m p Hpresent. unfold add_term.
    destruct (PTrieCode.get (X.encode (fst p)) m) as [q |] eqn:Hlookup;
      destruct (Pos.eq_dec key (X.encode (fst p))) as [Hsame | Hdifferent].
    - subst key. rewrite PTrie.get_set_same. eexists. reflexivity.
    - rewrite PTrie.get_set_other by exact Hdifferent.
      destruct Hpresent as [Hsame | Hpresent]; [contradiction | exact Hpresent].
    - subst key. rewrite PTrie.get_set_same. eexists. reflexivity.
    - rewrite PTrie.get_set_other by exact Hdifferent.
      destruct Hpresent as [Hsame | Hpresent]; [contradiction | exact Hpresent].
  Qed.

  (** Folding terms preserves every original key, including keys whose sum is zero. *)
  Lemma normalize_fold_present : forall ps m key,
    In key (map (fun p => X.encode (fst p)) ps) \/
      (exists q, PTrieCode.get key m = Some q) ->
    exists q, PTrieCode.get key (fold_left add_term ps m) = Some q.
  Proof.
    intro ps. induction ps as [| p ps IH]; intros m key Hpresent.
    - cbn [map In] in Hpresent. destruct Hpresent as [Hfalse | Hpresent];
        [contradiction | exact Hpresent].
    - cbn [fold_left]. apply IH. cbn [map In] in Hpresent.
      destruct Hpresent as [[Hsame | Hin] | Hin].
      + right. apply add_term_present. left. symmetry. exact Hsame.
      + left. exact Hin.
      + right. apply add_term_present. right. exact Hin.
  Qed.

  (** The dense coordinate list never repeats a key. *)
  Lemma variables_nodup : forall P, NoDup (variables P).
  Proof.
    intro P. unfold variables. apply normalization_values_nodup.
    apply normalize_fold_wf. apply normalization_empty.
  Qed.

  (** All raw occurrences have a dense coordinate, even after duplicate cancellation. *)
  Lemma variables_contains : forall P r x z,
    In r P -> In (x, z) (lhs r) -> In x (variables P).
  Proof.
    intros P r x z Hrow Hterm.
    assert (Hraw : In (x, z) (flat_map lhs P)).
    { apply in_flat_map. exists r. auto. }
    assert (Hkey : In (X.encode x)
      (map (fun p => X.encode (fst p)) (flat_map lhs P))).
    { apply in_map_iff. exists (x, z). split; [reflexivity | exact Hraw]. }
    destruct (normalize_fold_present (flat_map lhs P) PTrieCode.empty
      (X.encode x) (or_introl Hkey)) as [q Hget].
    assert (Hfst : fst q = x).
    { apply X.encode_inj. eapply normalize_fold_wf.
      - apply normalization_empty.
      - exact Hget. }
    unfold variables. apply in_map_iff. exists q. split; [exact Hfst |].
    rewrite karr_values_elements. apply in_map_iff.
    exists (X.encode x, q). split; [reflexivity |].
    apply (proj2 (PTrie.elements_spec _ _ _ _)). exact Hget.
  Qed.

  (** A variable absent from every stored occurrence has total coefficient zero. *)
  Lemma coefficient_absent : forall x ps,
    ~ In x (map fst ps) -> coefficient x ps = 0%Z.
  Proof.
    intros x ps. induction ps as [| [y z] ps IH]; intro Habsent; [reflexivity |].
    cbn [map fst In] in Habsent. unfold coefficient in *. cbn [fold_right fst snd].
    destruct (X.eqb_spec x y) as [Hsame | Hdifferent].
    - subst y. exfalso. apply Habsent. left. reflexivity.
    - apply IH. intro Hin. apply Habsent. right. exact Hin.
  Qed.

  (** Combining a coordinate list with its mapped values is ordinary pair mapping. *)
  Lemma combine_coordinate_map : forall xs (f : X.t -> Z),
    List.combine xs (map f xs) = map (fun x => (x, f x)) xs.
  Proof.
    intro xs. induction xs as [| x xs IH]; intro f; cbn; [reflexivity |].
    now rewrite IH.
  Qed.

  (** A unique coordinate carries exactly its assigned coefficient. *)
  Lemma coefficient_coordinates : forall xs (f : X.t -> Z) x,
    NoDup xs -> In x xs -> coefficient x (map (fun y => (y, f y)) xs) = f x.
  Proof.
    intro xs. induction xs as [| y xs IH]; intros f x Hunique Hin;
      [contradiction |].
    inversion Hunique as [| y' xs' Hnot Htail]; subst y' xs'.
    cbn [map]. unfold coefficient at 1. cbn [fold_right fst snd].
    destruct (X.eqb_spec x y) as [Hsame | Hdifferent].
    - subst x.
      assert (Hzero : coefficient y (map (fun z => (z, f z)) xs) = 0%Z).
      { apply coefficient_absent. rewrite map_map.
        change (~ In y (map (fun z => z) xs)). rewrite map_id. exact Hnot. }
      change ((f y + coefficient y (map (fun z => (z, f z)) xs))%Z = f y).
      rewrite Hzero. ring.
    - apply IH; [exact Htail |]. destruct Hin as [Hsame | Hin];
        [congruence | exact Hin].
  Qed.

  (** Filtering literal zero coefficients leaves every coefficient unchanged. *)
  Lemma coefficient_nonzero : forall x ps,
    coefficient x (filter (fun p => negb (Z.eqb (snd p) 0)) ps) = coefficient x ps.
  Proof.
    intros x ps. rewrite !coefficient_as_eval. apply eval_coef_nonzero.
  Qed.

  (** Sparse reconstruction of a dense row preserves all variable coefficients. *)
  Lemma dense_sparse_coefficient : forall xs r x,
    NoDup xs -> (forall y z, In (y, z) (lhs r) -> In y xs) ->
    coefficient x (sparse xs (dense xs r)) = coefficient x (lhs r).
  Proof.
    intros xs r x Hunique Hsupport. unfold sparse, dense.
    rewrite coefficient_nonzero, combine_coordinate_map.
    assert (Hdec : {In x xs} + {~ In x xs}).
    { apply in_dec. intros a b. destruct (X.eqb_spec a b); auto. }
    destruct Hdec as [Hin | Habsent].
    - now apply coefficient_coordinates.
    - rewrite coefficient_absent.
      + symmetry. apply coefficient_absent. intro Hin.
        apply in_map_iff in Hin as [[y z] [Hsame Hin]]. cbn [fst] in Hsame.
        subst y. apply Habsent. now apply Hsupport with (z := z).
      + rewrite map_map. change (~ In x (map (fun y => y) xs)).
        now rewrite map_id.
  Qed.

  (** Dense reconstruction of an input row preserves its raw total coefficients. *)
  Lemma variables_dense_coefficient : forall P r x, In r P ->
    coefficient x (sparse (variables P) (dense (variables P) r)) =
      coefficient x (lhs r).
  Proof.
    intros P r x Hin. apply dense_sparse_coefficient; [apply variables_nodup |].
    intros y z Hterm. now apply variables_contains with (r := r) (z := z).
  Qed.

  Lemma coefficient_cons : forall x y a ps,
    coefficient x ((y, a) :: ps) =
      ((if X.eqb x y then a else 0%Z) + coefficient x ps)%Z.
  Proof.
    intros x y a ps. unfold coefficient. cbn [fold_right fst snd].
    destruct (X.eqb x y); ring.
  Qed.

  Lemma coefficient_app : forall x ps qs,
    coefficient x (ps ++ qs) = (coefficient x ps + coefficient x qs)%Z.
  Proof.
    intros x ps qs. rewrite !coefficient_as_eval. apply eval_coef_app.
  Qed.

  Lemma coefficient_scale : forall x a ps,
    coefficient x (map (fun p => (fst p, (a * snd p)%Z)) ps) =
      (a * coefficient x ps)%Z.
  Proof.
    intros x a ps. rewrite !coefficient_as_eval. apply eval_coef_scale.
  Qed.

  Lemma coefficient_filter : forall x y ps,
    coefficient y (filter (fun p => negb (X.eqb x (fst p))) ps) =
      if X.eqb y x then 0%Z else coefficient y ps.
  Proof.
    intros x y ps. induction ps as [|[z a] ps IH].
    - cbn [filter coefficient]. destruct (X.eqb y x); reflexivity.
    - destruct (X.eqb_spec y x) as [Hyx|Hyx].
      + subst y. cbn [filter fst].
        destruct (X.eqb x z) eqn:Hxz; cbn [negb].
        * exact IH.
        * rewrite coefficient_cons, Hxz. exact IH.
      + cbn [filter fst]. destruct (X.eqb_spec x z) as [Hxz|Hxz].
        * subst z. cbn [negb]. rewrite IH, coefficient_cons.
          destruct (X.eqb_spec y x) as [Heq|Hneq]; [contradiction|reflexivity].
        * cbn [negb]. rewrite !coefficient_cons, IH. reflexivity.
  Qed.

  Lemma eval_coef_split : forall x ps (v : X.t -> Z),
    eval_coef v ps = (coefficient x ps * v x +
      eval_coef v (filter (fun p => negb (X.eqb x (fst p))) ps))%Z.
  Proof.
    intros x ps v. induction ps as [|[y a] ps IH].
    - reflexivity.
    - rewrite coefficient_cons. cbn [filter fst].
      destruct (X.eqb_spec x y) as [Hxy|Hxy].
      + subst y.
        change (a * v x + eval_coef v ps = (a + coefficient x ps) * v x +
          eval_coef v (filter (fun p => negb (X.eqb x (fst p))) ps))%Z.
        rewrite IH. ring.
      + change (a * v y + eval_coef v ps = coefficient x ps * v x +
          (a * v y + eval_coef v (filter (fun p => negb (X.eqb x (fst p))) ps)))%Z.
        rewrite IH. ring.
  Qed.

  Lemma eval_coef_zero : forall ps (v : X.t -> Z),
    (forall x, coefficient x ps = 0%Z) -> eval_coef v ps = 0%Z.
  Proof.
    refine (well_founded_induction
      (well_founded_ltof _ (@length (X.t * Z))) _ _).
    intros ps IH v Hzero. destruct ps as [|[x a] ps].
    - reflexivity.
    - rewrite (eval_coef_split x ((x, a) :: ps) v), Hzero.
      rewrite Z.mul_0_l, Z.add_0_l. apply IH.
      + unfold ltof. cbn [filter fst length].
        rewrite key_eqb_refl. cbn [negb].
        pose proof (filter_length_le (fun p => negb (X.eqb x (fst p))) ps). lia.
      + intro y. rewrite coefficient_filter.
        destruct (X.eqb y x); [reflexivity|apply Hzero].
  Qed.

  Lemma eval_coef_ext : forall ps qs (v : X.t -> Z),
    (forall x, coefficient x ps = coefficient x qs) -> eval_coef v ps = eval_coef v qs.
  Proof.
    intros ps qs v Heq.
    assert (Hzero : forall x,
      coefficient x (ps ++ map (fun p => (fst p, ((-1) * snd p)%Z)) qs) = 0%Z).
    { intro x. rewrite coefficient_app, coefficient_scale, Heq. ring. }
    pose proof (eval_coef_zero _ v Hzero) as Heval.
    rewrite eval_coef_app, eval_coef_scale in Heval. lia.
  Qed.

  Lemma eval_coef_app_Q : forall (v : X.t -> Q) ps qs,
    (karr_eval_coef_Q v (ps ++ qs) == karr_eval_coef_Q v ps + karr_eval_coef_Q v qs)%Q.
  Proof.
    intros v ps qs. apply karr_qsum_app.
  Qed.

  Lemma eval_coef_scale_Q : forall a ps (v : X.t -> Q),
    (karr_eval_coef_Q v (map (fun p => (fst p, (a * snd p)%Z)) ps) ==
      inject_Z a * karr_eval_coef_Q v ps)%Q.
  Proof.
    intros a ps v. induction ps as [|[x z] ps IH].
    - change (0 == inject_Z a * 0)%Q. ring.
    - change (inject_Z (a * z) * v x +
        karr_eval_coef_Q v (map (fun p => (fst p, (a * snd p)%Z)) ps) ==
        inject_Z a * (inject_Z z * v x + karr_eval_coef_Q v ps))%Q.
      rewrite inject_Z_mult. setoid_rewrite IH. ring.
  Qed.

  Lemma eval_coef_split_Q : forall x ps (v : X.t -> Q),
    (karr_eval_coef_Q v ps == inject_Z (coefficient x ps) * v x +
      karr_eval_coef_Q v (filter (fun p => negb (X.eqb x (fst p))) ps))%Q.
  Proof.
    intros x ps v. induction ps as [|[y a] ps IH].
    - change (0 == 0 * v x + 0)%Q. ring.
    - rewrite coefficient_cons. cbn [filter fst].
      destruct (X.eqb_spec x y) as [Hxy|Hxy].
      + subst y.
        change (inject_Z a * v x + karr_eval_coef_Q v ps ==
          inject_Z (a + coefficient x ps) * v x +
          karr_eval_coef_Q v (filter (fun p => negb (X.eqb x (fst p))) ps))%Q.
        rewrite inject_Z_plus. setoid_rewrite IH. ring.
      + change (inject_Z a * v y + karr_eval_coef_Q v ps ==
          inject_Z (coefficient x ps) * v x + (inject_Z a * v y +
          karr_eval_coef_Q v (filter (fun p => negb (X.eqb x (fst p))) ps)))%Q.
        setoid_rewrite IH. ring.
  Qed.

  Lemma eval_coef_zero_Q : forall ps (v : X.t -> Q),
    (forall x, coefficient x ps = 0%Z) -> (karr_eval_coef_Q v ps == 0)%Q.
  Proof.
    refine (well_founded_induction
      (well_founded_ltof _ (@length (X.t * Z))) _ _).
    intros ps IH v Hzero. destruct ps as [|[x a] ps].
    - reflexivity.
    - setoid_rewrite (eval_coef_split_Q x ((x, a) :: ps) v).
      rewrite Hzero. setoid_rewrite Qmult_0_l. setoid_rewrite Qplus_0_l. apply IH.
      + unfold ltof. cbn [filter fst length]. rewrite key_eqb_refl. cbn [negb].
        pose proof (filter_length_le (fun p => negb (X.eqb x (fst p))) ps). lia.
      + intro y. rewrite coefficient_filter.
        destruct (X.eqb y x); [reflexivity|apply Hzero].
  Qed.

  Lemma eval_coef_ext_Q : forall ps qs (v : X.t -> Q),
    (forall x, coefficient x ps = coefficient x qs) ->
    (karr_eval_coef_Q v ps == karr_eval_coef_Q v qs)%Q.
  Proof.
    intros ps qs v Heq.
    assert (Hzero : forall x,
      coefficient x (ps ++ map (fun p => (fst p, ((-1) * snd p)%Z)) qs) = 0%Z).
    { intro x. rewrite coefficient_app, coefficient_scale, Heq. ring. }
    pose proof (eval_coef_zero_Q _ v Hzero) as Heval.
    setoid_rewrite eval_coef_app_Q in Heval.
    setoid_rewrite eval_coef_scale_Q in Heval.
    change (karr_eval_coef_Q v ps + (-1) * karr_eval_coef_Q v qs == 0)%Q in Heval.
    apply (proj1 (Qplus_inj_r (karr_eval_coef_Q v ps) (karr_eval_coef_Q v qs)
      (- karr_eval_coef_Q v qs)%Q)).
    setoid_replace (karr_eval_coef_Q v qs + - karr_eval_coef_Q v qs)%Q with 0%Q by ring.
    setoid_replace (karr_eval_coef_Q v ps + - karr_eval_coef_Q v qs)%Q
      with (karr_eval_coef_Q v ps + (-1) * karr_eval_coef_Q v qs)%Q by ring.
    exact Heval.
  Qed.

  Lemma dense_sparse_eval : forall xs r v,
    NoDup xs -> (forall y z, In (y, z) (lhs r) -> In y xs) ->
    eval_coef v (sparse xs (dense xs r)) = eval_coef v (lhs r).
  Proof.
    intros xs r v Hunique Hsupport. apply eval_coef_ext. intro x.
    now apply dense_sparse_coefficient.
  Qed.

  Lemma dense_sparse_eval_Q : forall xs r v,
    NoDup xs -> (forall y z, In (y, z) (lhs r) -> In y xs) ->
    (karr_eval_coef_Q v (sparse xs (dense xs r)) == karr_eval_coef_Q v (lhs r))%Q.
  Proof.
    intros xs r v Hunique Hsupport. apply eval_coef_ext_Q. intro x.
    now apply dense_sparse_coefficient.
  Qed.

  (** Finite coordinate values extend to a total rational store. *)
  Definition coordinate_store (xs : list X.t) (qs : list Q) (x : X.t) : Q :=
    fold_right (fun p q => if X.eqb x (fst p) then snd p else q) 0%Q
      (List.combine xs qs).

  Lemma coordinate_store_values : forall xs qs,
    NoDup xs -> length xs = length qs -> map (coordinate_store xs qs) xs = qs.
  Proof.
    intro xs. induction xs as [|x xs IH]; intros [|q qs] Hunique Hlength;
      cbn [length] in Hlength; try discriminate; [reflexivity |].
    inversion Hunique as [|x' xs' Hnot Htail]; subst x' xs'.
    cbn [map]. f_equal.
    - unfold coordinate_store. cbn [List.combine fold_right fst snd].
      now rewrite key_eqb_refl.
    - transitivity (map (coordinate_store xs qs) xs).
      + apply map_ext_in. intros y Hin. unfold coordinate_store.
        cbn [List.combine fold_right fst snd].
        destruct (X.eqb_spec y x) as [Hsame | Hdifferent]; [|reflexivity].
        subst y. contradiction.
      + apply IH; [exact Htail |lia].
  Qed.

  Lemma dense_combine_eval_Q : forall xs zs (v : X.t -> Q),
    (karr_eval (map v xs) zs == karr_eval_coef_Q v (List.combine xs zs))%Q.
  Proof.
    intro xs. induction xs as [|x xs IH]; intros [|z zs] v;
      cbn [map karr_eval List.combine karr_eval_coef_Q karr_qsum fold_right fst snd];
      try reflexivity.
    apply Qplus_comp; [reflexivity |apply IH].
  Qed.

  Lemma dense_eval_Q : forall xs r (v : X.t -> Q),
    NoDup xs -> (forall y z, In (y, z) (lhs r) -> In y xs) ->
    (karr_eval (map v xs) (dense xs r) == karr_eval_coef_Q v (lhs r))%Q.
  Proof.
    intros xs r v Hunique Hsupport.
    pose proof (dense_sparse_eval_Q xs r v Hunique Hsupport) as Heval.
    unfold sparse in Heval. setoid_rewrite eval_coef_nonzero_Q in Heval.
    setoid_rewrite dense_combine_eval_Q. exact Heval.
  Qed.

  Lemma coordinate_dense_eval_Q : forall xs qs r,
    NoDup xs -> length xs = length qs ->
    (forall y z, In (y, z) (lhs r) -> In y xs) ->
    (karr_eval qs (dense xs r) ==
      karr_eval_coef_Q (coordinate_store xs qs) (lhs r))%Q.
  Proof.
    intros xs qs r Hunique Hlength Hsupport.
    rewrite <- (coordinate_store_values xs qs Hunique Hlength) at 1.
    now apply dense_eval_Q.
  Qed.

  (** A mathematical weighted sum over the original rows. *)
  Definition row_sum (P : list (lcons X.t)) (ms : list Z)
      (entry : lcons X.t -> Z) : Z :=
    fold_right Z.add 0%Z
      (map (fun pm => (snd pm * entry (fst pm))%Z) (List.combine P ms)).

  (** Source inequalities have zero weight in equality elimination. *)
  Definition equality_weights (P : list (lcons X.t)) (ms : list Z) : Prop :=
    Forall2 (fun p m => lrel p = RLe -> m = 0%Z) P ms.

  (** Removed columns remain zero in the full original coordinate system. *)
  Definition row_tracks (P : list (lcons X.t)) (xs : list X.t)
      (target : lcons X.t) (offset : nat) (r : karr_row) : Prop :=
    equality_weights P (kweight r) /\
    repeat 0%Z offset ++ kcoeff r =
      map (fun x => (C.comb_coef P (kweight r) x +
        kscale r * coefficient x (lhs target))%Z) xs /\
    kright r = (C.comb_rhs P (kweight r) + kscale r * rhs target)%Z.

  Lemma equality_weights_length : forall P ms,
    equality_weights P ms -> length P = length ms.
  Proof.
    intros P ms Hweights. induction Hweights; cbn; congruence.
  Qed.

  Lemma equality_weights_admissible : forall P ms,
    equality_weights P ms -> C.admissible P ms.
  Proof.
    intros P ms Hweights. split; [now apply equality_weights_length |].
    induction Hweights; constructor; auto. intro Hle. specialize (H Hle). lia.
  Qed.

  Lemma equality_weights_comb_eq : forall P ms,
    equality_weights P ms -> C.comb_eq P ms = true.
  Proof.
    intros P ms Hweights. induction Hweights as [|p m P ms Hhead Htail IH];
      [reflexivity |].
    change ((match lrel p with REq => true | RLe => Z.eqb m 0 end &&
      C.comb_eq P ms) = true).
    rewrite IH. destruct (lrel p) eqn:Hrel; [reflexivity |].
    rewrite (Hhead eq_refl). reflexivity.
  Qed.

  Lemma row_sum_scale : forall P ms entry a,
    row_sum P (map (fun z => (a * z)%Z) ms) entry = (a * row_sum P ms entry)%Z.
  Proof.
    intro P. induction P as [| p P IH]; intros [|m ms] entry a;
      unfold row_sum in *; cbn [List.combine map fold_right fst snd]; try ring.
    rewrite IH. ring.
  Qed.

  Lemma row_sum_cross : forall P ms ns entry a b,
    length ms = length ns ->
    row_sum P (karr_cross a b ms ns) entry =
      (a * row_sum P ms entry - b * row_sum P ns entry)%Z.
  Proof.
    intro P. induction P as [|p P IH]; intros [|m ms] [|n ns] entry a b Hlength;
      cbn [length] in Hlength; try discriminate;
      unfold row_sum in *; cbn [karr_cross List.combine map fold_right fst snd]; try ring.
    rewrite IH by lia. ring.
  Qed.

  Lemma comb_coef_scale : forall P ms a x,
    C.comb_coef P (map (fun z => (a * z)%Z) ms) x = (a * C.comb_coef P ms x)%Z.
  Proof.
    intros P ms a x.
    change (row_sum P (map (fun z => (a * z)%Z) ms)
      (fun r => C.coef_of x (lhs r)) =
      (a * row_sum P ms (fun r => C.coef_of x (lhs r)))%Z).
    apply row_sum_scale.
  Qed.

  Lemma comb_rhs_scale : forall P ms a,
    C.comb_rhs P (map (fun z => (a * z)%Z) ms) = (a * C.comb_rhs P ms)%Z.
  Proof.
    intros P ms a.
    change (row_sum P (map (fun z => (a * z)%Z) ms) rhs =
      (a * row_sum P ms rhs)%Z).
    apply row_sum_scale.
  Qed.

  Lemma comb_coef_cross : forall P ms ns a b x,
    length ms = length ns ->
    C.comb_coef P (karr_cross a b ms ns) x =
      (a * C.comb_coef P ms x - b * C.comb_coef P ns x)%Z.
  Proof.
    intros P ms ns a b x Hlength.
    change (row_sum P (karr_cross a b ms ns) (fun r => C.coef_of x (lhs r)) =
      (a * row_sum P ms (fun r => C.coef_of x (lhs r)) -
       b * row_sum P ns (fun r => C.coef_of x (lhs r)))%Z).
    now apply row_sum_cross.
  Qed.

  Lemma comb_rhs_cross : forall P ms ns a b,
    length ms = length ns ->
    C.comb_rhs P (karr_cross a b ms ns) =
      (a * C.comb_rhs P ms - b * C.comb_rhs P ns)%Z.
  Proof.
    intros P ms ns a b Hlength.
    change (row_sum P (karr_cross a b ms ns) rhs =
      (a * row_sum P ms rhs - b * row_sum P ns rhs)%Z).
    now apply row_sum_cross.
  Qed.

  Lemma equality_weights_cross : forall P ms ns a b,
    equality_weights P ms -> equality_weights P ns ->
    equality_weights P (karr_cross a b ms ns).
  Proof.
    intros P ms ns a b Hms. revert ns.
    induction Hms as [|p m P ms Hhead Htail IH]; intros ns Hns;
      inversion Hns as [|p' n P' ns' Hhead' Htail']; subst; cbn [karr_cross].
    - constructor.
    - constructor; [|now apply IH]. intro Hle.
      rewrite (Hhead Hle), (Hhead' Hle). ring.
  Qed.

  Lemma equality_weights_factor : forall P ms factor,
    factor <> 0%Z -> equality_weights P (map (fun z => (factor * z)%Z) ms) ->
    equality_weights P ms.
  Proof.
    intro P. induction P as [|p P IH]; intros [|m ms] factor Hnonzero Hweights;
      inversion Hweights as [|p' m' P' ms' Hhead Htail]; subst.
    - constructor.
    - constructor; [|now apply IH with (factor := factor)].
      intro Hle. specialize (Hhead Hle). nia.
  Qed.

  Lemma scale_list_injective : forall factor xs ys,
    factor <> 0%Z ->
    map (fun z => (factor * z)%Z) xs = map (fun z => (factor * z)%Z) ys -> xs = ys.
  Proof.
    intros factor xs. induction xs as [|x xs IH]; intros [|y ys] Hnonzero Hsame;
      cbn [map] in Hsame; try discriminate; [reflexivity |].
    injection Hsame as Hhead Htail. f_equal; [nia | now apply IH].
  Qed.

  Lemma scale_zero_prefix : forall factor offset zs,
    map (fun z => (factor * z)%Z) (repeat 0%Z offset ++ zs) =
      repeat 0%Z offset ++ map (fun z => (factor * z)%Z) zs.
  Proof.
    intros factor offset. induction offset as [|offset IH]; intro zs;
      cbn [repeat app map]; [reflexivity |].
    rewrite Z.mul_0_r, IH. reflexivity.
  Qed.

  Lemma cross_zero_prefix : forall a b offset xs ys,
    karr_cross a b (repeat 0%Z offset ++ xs) (repeat 0%Z offset ++ ys) =
      repeat 0%Z offset ++ karr_cross a b xs ys.
  Proof.
    intros a b offset. induction offset as [|offset IH]; intros xs ys;
      cbn [repeat app karr_cross]; [reflexivity |].
    rewrite !Z.mul_0_r, Z.sub_0_r, IH. reflexivity.
  Qed.

  Lemma cross_coordinate_map : forall xs (f g : X.t -> Z) a b,
    karr_cross a b (map f xs) (map g xs) =
      map (fun x => (a * f x - b * g x)%Z) xs.
  Proof.
    intro xs. induction xs as [|x xs IH]; intros f g a b; cbn; [reflexivity |].
    now rewrite IH.
  Qed.

  Lemma row_tracks_factor : forall P xs target offset factor r s,
    factor <> 0%Z -> karr_multiple factor r s -> row_tracks P xs target offset s ->
    row_tracks P xs target offset r.
  Proof.
    intros P xs target offset factor r s Hnonzero Hmultiple Htracks.
    destruct Hmultiple as [Hcoeff [Hright [Hweight Hscale]]].
    destruct Htracks as [Hweights [Hcoordinates Hrhs]].
    split.
    - apply equality_weights_factor with (factor := factor); [exact Hnonzero |].
      now rewrite Hweight.
    - split.
      + apply scale_list_injective with (factor := factor); [exact Hnonzero |].
        rewrite scale_zero_prefix, Hcoeff, Hcoordinates, map_map.
        apply map_ext. intro x. rewrite <- Hweight, comb_coef_scale, <- Hscale. ring.
      + rewrite <- Hweight, comb_rhs_scale, <- Hscale, <- Hright in Hrhs. nia.
  Qed.

  Lemma row_tracks_divide : forall P xs target offset divisor r,
    row_tracks P xs target offset r ->
    row_tracks P xs target offset (karr_divide divisor r).
  Proof.
    intros P xs target offset divisor r Htracks.
    destruct (karr_divide_factor divisor r) as [factor [Hnonzero Hmultiple]].
    now apply row_tracks_factor with (factor := factor) (s := r).
  Qed.

  Lemma row_tracks_reduce : forall P xs target offset divisor a b p r,
    row_tracks P xs target offset p -> row_tracks P xs target offset r ->
    row_tracks P xs target offset (karr_reduce divisor a b p r).
  Proof.
    intros P xs target offset divisor a b p r Hp Hr.
    unfold karr_reduce. apply row_tracks_divide.
    destruct Hp as [Hpw [Hpc Hpr]]. destruct Hr as [Hrw [Hrc Hrr]].
    assert (Hlength : length (kweight r) = length (kweight p)).
    { rewrite <- (equality_weights_length _ _ Hrw),
        <- (equality_weights_length _ _ Hpw). reflexivity. }
    split.
    - cbn [kweight]. now apply equality_weights_cross.
    - cbn [kcoeff kweight kright kscale]. split.
      + rewrite <- cross_zero_prefix, Hrc, Hpc, cross_coordinate_map.
        apply map_ext. intro x. rewrite comb_coef_cross by exact Hlength. ring.
      + rewrite comb_rhs_cross by exact Hlength. rewrite Hrr, Hpr. ring.
  Qed.

  Lemma zero_prefix_succ : forall offset zs,
    repeat 0%Z (S offset) ++ zs = repeat 0%Z offset ++ 0%Z :: zs.
  Proof.
    intro offset. induction offset as [|offset IH]; intro zs; [reflexivity |].
    change (0%Z :: (repeat 0%Z (S offset) ++ zs) =
      0%Z :: (repeat 0%Z offset ++ 0%Z :: zs)).
    f_equal. apply IH.
  Qed.

  Lemma row_tracks_tail : forall P xs target offset r zs,
    row_tracks P xs target offset r -> kcoeff r = 0%Z :: zs ->
    row_tracks P xs target (S offset) (karr_tail r).
  Proof.
    intros P xs target offset r zs [Hweights [Hcoordinates Hrhs]] Hcoeff.
    unfold row_tracks. cbn [karr_tail kweight kcoeff kright kscale].
    split; [exact Hweights |]. split; [|exact Hrhs].
    rewrite Hcoeff. cbn [tl]. rewrite zero_prefix_succ. now rewrite <- Hcoeff.
  Qed.

  Lemma row_tracks_restore : forall P xs target offset r,
    row_tracks P xs target (S offset) r ->
    row_tracks P xs target offset (karr_restore r).
  Proof.
    intros P xs target offset r [Hweights [Hcoordinates Hrhs]].
    unfold row_tracks. cbn [karr_restore kweight kcoeff kright kscale].
    split; [exact Hweights |]. split; [|exact Hrhs].
    now rewrite <- zero_prefix_succ.
  Qed.

  Lemma divide_scale_zero : forall divisor r,
    kscale r = 0%Z -> kscale (karr_divide divisor r) = 0%Z.
  Proof.
    intros divisor r Hzero.
    destruct (karr_divide_factor divisor r) as [factor [Hnonzero Hmultiple]].
    destruct Hmultiple as [_ [_ [_ Hscale]]]. rewrite Hzero in Hscale. nia.
  Qed.

  Lemma reduce_scale_zero : forall divisor a b p r,
    kscale p = 0%Z -> kscale r = 0%Z ->
    kscale (karr_reduce divisor a b p r) = 0%Z.
  Proof.
    intros divisor a b p r Hp Hr. unfold karr_reduce. apply divide_scale_zero.
    cbn [kscale]. rewrite Hp, Hr. ring.
  Qed.

  Lemma reduce_scale_nonzero : forall divisor a b p r,
    a <> 0%Z -> kscale p = 0%Z -> kscale r <> 0%Z ->
    kscale (karr_reduce divisor a b p r) <> 0%Z.
  Proof.
    intros divisor a b p r Ha Hp Hr Hzero. unfold karr_reduce in Hzero.
    destruct (karr_divide_factor divisor
      (KRow (karr_cross a b (kcoeff r) (kcoeff p))
        (a * kright r - b * kright p)%Z
        (karr_cross a b (kweight r) (kweight p))
        (a * kscale r - b * kscale p)%Z)) as [factor [_ Hmultiple]].
    destruct Hmultiple as [_ [_ [_ Hscale]]].
    rewrite Hzero in Hscale. cbn [kscale] in Hscale. rewrite Hp in Hscale. nia.
  Qed.

  Lemma equality_weights_scale : forall P ms factor,
    equality_weights P ms ->
    equality_weights P (map (fun z => (factor * z)%Z) ms).
  Proof.
    intros P ms factor Hweights.
    induction Hweights as [|p m P ms Hhead Htail IH]; cbn [map]; constructor; auto.
    intro Hle. rewrite (Hhead Hle). ring.
  Qed.

  Lemma comb_coef_zero : forall P ms x,
    (forall r, In r P -> coefficient x (lhs r) = 0%Z) -> C.comb_coef P ms x = 0%Z.
  Proof.
    intro P. induction P as [|p P IH]; intros [|m ms] x Hzero;
      try reflexivity.
    change ((m * coefficient x (lhs p) + C.comb_coef P ms x)%Z = 0%Z).
    rewrite Hzero by now left. rewrite IH; [ring |].
    intros r Hin. apply Hzero. now right.
  Qed.

  Lemma row_tracks_zero_coeff : forall P xs target r,
    row_tracks P xs target 0 r ->
    (forall s, In s (target :: P) ->
      forall x z, In (x, z) (lhs s) -> In x xs) ->
    karr_zero r = true ->
    forall x, (C.comb_coef P (kweight r) x +
      kscale r * coefficient x (lhs target) = 0)%Z.
  Proof.
    intros P xs target r [_ [Hcoordinates _]] Hsupport Hzero x.
    cbn [repeat app] in Hcoordinates. unfold karr_zero in Hzero.
    assert (Hdec : {In x xs} + {~ In x xs}).
    { apply in_dec. intros a b. destruct (X.eqb_spec a b); auto. }
    destruct Hdec as [Hin | Habsent].
    - assert (Hz : Z.eqb 0 (C.comb_coef P (kweight r) x +
        kscale r * coefficient x (lhs target)) = true).
      { apply (proj1 (forallb_forall _ _) Hzero).
        rewrite Hcoordinates. apply in_map_iff. exists x.
        split; [reflexivity |exact Hin]. }
      apply Z.eqb_eq in Hz. lia.
    - assert (Hcoeff : forall s, In s (target :: P) -> coefficient x (lhs s) = 0%Z).
      { intros s Hrow. apply coefficient_absent. intro Hin.
        apply in_map_iff in Hin as [[y z] [Hsame Hin]]. cbn [fst] in Hsame.
        subst y. apply Habsent. now apply Hsupport with (s := s) (z := z). }
      rewrite Hcoeff by now left. rewrite comb_coef_zero; [ring |].
      intros s Hin. apply Hcoeff. now right.
  Qed.

  (** A zero target residual reconstructs an exact certificate accepted by every checker. *)
  Lemma row_tracks_check_entails : forall P xs target r,
    row_tracks P xs target 0 r ->
    (forall s, In s (target :: P) ->
      forall x z, In (x, z) (lhs s) -> In x xs) ->
    karr_zero r = true -> kscale r <> 0%Z ->
    (match lrel target with
     | REq => kright r = 0%Z
     | RLe => (0 <= (if (kscale r <? 0)%Z then -1 else 1) * kright r)%Z
     end) ->
    C.check_entails P target
      (Cert (map (fun z => (-(if (kscale r <? 0)%Z then -1 else 1) * z)%Z)
        (kweight r)) (Z.abs (kscale r)) false) = true.
  Proof.
    intros P xs target r Htracks Hsupport Hzero Hnonzero Hright.
    pose proof (row_tracks_zero_coeff P xs target r Htracks Hsupport Hzero) as Hcoeff.
    destruct Htracks as [Hweights [_ Hrhs]].
    set (sign := if (kscale r <? 0)%Z then (-1)%Z else 1%Z) in *.
    assert (Hsign : (sign * kscale r = Z.abs (kscale r))%Z).
    { apply coefficient_sign_abs. }
    apply C.check_entails_complete.
    - apply equality_weights_admissible. now apply equality_weights_scale.
    - destruct (kscale r); cbn in *; lia.
    - intro x. rewrite comb_coef_scale. specialize (Hcoeff x).
      change ((-sign * C.comb_coef P (kweight r) x)%Z =
        (Z.abs (kscale r) * coefficient x (lhs target))%Z).
      nia.
    - destruct (lrel target) eqn:Hrel.
      + split.
        * apply equality_weights_comb_eq. now apply equality_weights_scale.
        * rewrite comb_rhs_scale. nia.
      + rewrite comb_rhs_scale. nia.
  Qed.

  (** A contradictory tracked equality is accepted by every empty-system checker. *)
  Lemma row_tracks_check_empty : forall P xs target r,
    row_tracks P xs target 0 r ->
    (forall s, In s (target :: P) ->
      forall x z, In (x, z) (lhs s) -> In x xs) ->
    karr_zero r = true -> kscale r = 0%Z -> kright r <> 0%Z ->
    C.check_empty P (kweight r) = true.
  Proof.
    intros P xs target r Htracks Hsupport Hzero Hscale Hnonzero.
    pose proof (row_tracks_zero_coeff P xs target r Htracks Hsupport Hzero) as Hcoeff.
    destruct Htracks as [Hweights [_ Hrhs]].
    apply C.check_empty_complete.
    - now apply equality_weights_admissible.
    - intro x. specialize (Hcoeff x). rewrite Hscale in Hcoeff. lia.
    - right. split; [now apply equality_weights_comb_eq |].
      rewrite Hscale in Hrhs. lia.
  Qed.

  Lemma equality_weights_zero : forall P,
    equality_weights P (repeat 0%Z (length P)).
  Proof.
    intro P. induction P as [|p P IH]; cbn [length repeat]; constructor; auto.
  Qed.

  Lemma row_sum_zero : forall P entry,
    row_sum P (repeat 0%Z (length P)) entry = 0%Z.
  Proof.
    intro P. induction P as [|p P IH]; intro entry; [reflexivity |].
    change ((0 * entry p + row_sum P (repeat 0%Z (length P)) entry)%Z = 0%Z).
    rewrite IH. ring.
  Qed.

  Lemma row_sum_unit : forall P index p entry,
    nth_error P index = Some p -> row_sum P (karr_unit (length P) index) entry = entry p.
  Proof.
    intro P. induction P as [|r P IH]; intros [|index] p entry Hnth;
      cbn [nth_error] in Hnth; try discriminate.
    - injection Hnth as Hsame. subst p.
      change ((1 * entry r + row_sum P (repeat 0%Z (length P)) entry)%Z = entry r).
      rewrite row_sum_zero. ring.
    - change ((0 * entry r + row_sum P (karr_unit (length P) index) entry)%Z = entry p).
      rewrite (IH _ _ _ Hnth). ring.
  Qed.

  Lemma equality_weights_unit : forall P index p,
    nth_error P index = Some p -> lrel p = REq ->
    equality_weights P (karr_unit (length P) index).
  Proof.
    intro P. induction P as [|r P IH]; intros [|index] p Hnth Hrel;
      cbn [nth_error] in Hnth; try discriminate.
    - injection Hnth as Hsame. subst p. cbn [length karr_unit]. constructor.
      + intro Hle. congruence.
      + apply equality_weights_zero.
    - cbn [length karr_unit]. constructor; [auto |]. now apply IH with (p := p).
  Qed.

  Lemma comb_coef_unit : forall P index p x,
    nth_error P index = Some p ->
    C.comb_coef P (karr_unit (length P) index) x = coefficient x (lhs p).
  Proof.
    intros P index p x Hnth.
    change (row_sum P (karr_unit (length P) index)
      (fun r => coefficient x (lhs r)) = coefficient x (lhs p)).
    exact (row_sum_unit P index p (fun r => coefficient x (lhs r)) Hnth).
  Qed.

  Lemma comb_rhs_unit : forall P index p,
    nth_error P index = Some p -> C.comb_rhs P (karr_unit (length P) index) = rhs p.
  Proof.
    intros P index p Hnth.
    change (row_sum P (karr_unit (length P) index) rhs = rhs p).
    exact (row_sum_unit P index p rhs Hnth).
  Qed.

  Lemma seed_rows_member : forall xs total rows index r,
    In r (seed_rows xs total index rows) ->
    exists i p, nth_error rows i = Some p /\ lrel p = REq /\
      r = KRow (dense xs p) (rhs p) (karr_unit total (index + i)) 0%Z.
  Proof.
    intros xs total rows. induction rows as [|p rows IH]; intros index r Hin;
      [contradiction |].
    cbn [seed_rows] in Hin. destruct (lrel p) eqn:Hrel.
    - cbn [In] in Hin. destruct Hin as [Hsame | Hin].
      + subst r. exists 0, p. split; [reflexivity |]. split; [exact Hrel |].
        now rewrite Nat.add_0_r.
      + destruct (IH _ _ Hin) as [i [q [Hnth [Heq Hrow]]]].
        exists (S i), q. split; [exact Hnth |]. split; [exact Heq |].
        replace (index + S i) with (S index + i) by lia. exact Hrow.
    - destruct (IH _ _ Hin) as [i [q [Hnth [Heq Hrow]]]].
      exists (S i), q. split; [exact Hnth |]. split; [exact Heq |].
      replace (index + S i) with (S index + i) by lia. exact Hrow.
  Qed.

  Lemma seed_rows_tracks : forall P xs target,
    Forall (row_tracks P xs target 0)
      (seed_rows xs (length P) 0 (map normalize_row P)).
  Proof.
    intros P xs target. apply Forall_forall. intros r Hin.
    destruct (seed_rows_member _ _ _ _ _ Hin) as [i [p [Hnth [Hrel Hrow]]]].
    rewrite nth_error_map in Hnth.
    destruct (nth_error P i) as [q |] eqn:Hq; [|discriminate].
    injection Hnth as Hsame. subst p. subst r. cbn [Nat.add] in *.
    split.
    - cbn [kweight]. apply equality_weights_unit with (p := q);
        [exact Hq | exact Hrel].
    - cbn [repeat app kcoeff kweight kright kscale]. split.
      + unfold dense. cbn [normalize_row lhs]. apply map_ext. intro x.
        rewrite normalize_coef_coefficient, (comb_coef_unit _ _ _ _ Hq). ring.
      + cbn [normalize_row rhs]. rewrite (comb_rhs_unit _ _ _ Hq). ring.
  Qed.

  Lemma target_initial_tracks : forall P xs target,
    row_tracks P xs target 0
      (KRow (dense xs target) (rhs target) (repeat 0%Z (length P)) 1).
  Proof.
    intros P xs target. split; [apply equality_weights_zero |].
    cbn [repeat app kcoeff kweight kright kscale]. split.
    - unfold dense. apply map_ext. intro x.
      change (coefficient x (lhs target) =
        (row_sum P (repeat 0%Z (length P)) (fun r => coefficient x (lhs r)) +
          1 * coefficient x (lhs target))%Z).
      rewrite row_sum_zero. ring.
    - change (rhs target = (row_sum P (repeat 0%Z (length P)) rhs + 1 * rhs target)%Z).
      rewrite row_sum_zero. ring.
  Qed.

  Lemma row_tracks_width : forall P xs target offset r,
    row_tracks P xs target offset r -> offset + length (kcoeff r) = length xs.
  Proof.
    intros P xs target offset r [_ [Hcoordinates _]].
    pose proof (f_equal (@length Z) Hcoordinates) as Hlength.
    now rewrite length_app, repeat_length, length_map in Hlength.
  Qed.

  Lemma row_tracks_tail_head : forall P xs target offset r,
    row_tracks P xs target offset r -> offset < length xs -> karr_head r = 0%Z ->
    row_tracks P xs target (S offset) (karr_tail r).
  Proof.
    intros P xs target offset r Htracks Hroom Hzero.
    pose proof (row_tracks_width _ _ _ _ _ Htracks) as Hwidth.
    destruct (kcoeff r) as [|a zs] eqn:Hcoeff; [cbn [length] in Hwidth; lia |].
    unfold karr_head in Hzero. rewrite Hcoeff in Hzero. subst a.
    now apply row_tracks_tail with (zs := zs).
  Qed.

  Lemma target_tracks : forall P xs target rs previous r,
    Forall (row_tracks P xs target 0) rs -> row_tracks P xs target 0 r ->
    row_tracks P xs target 0 (karr_target rs previous r).
  Proof.
    intros P xs target rs. induction rs as [|p rs IH]; intros previous r Hbasis Hrow;
      [exact Hrow |].
    inversion Hbasis as [|p' rs' Hp Hrest]; subst p' rs'.
    cbn [karr_target]. destruct (karr_first (kcoeff p)) as [[i a] |].
    - apply IH; [exact Hrest |]. now apply row_tracks_reduce.
    - now apply IH.
  Qed.

  Lemma target_scale_nonzero : forall rs previous r,
    Forall (fun p => kscale p = 0%Z) rs -> kscale r <> 0%Z ->
    kscale (karr_target rs previous r) <> 0%Z.
  Proof.
    intro rs. induction rs as [|p rs IH]; intros previous r Hbasis Hrow;
      [exact Hrow |].
    inversion Hbasis as [|p' rs' Hp Hrest]; subst p' rs'.
    cbn [karr_target]. destruct (karr_first (kcoeff p)) as [[i a] |] eqn:Hfirst.
    - apply IH; [exact Hrest |]. apply reduce_scale_nonzero.
      + now apply karr_first_nonzero with (zs := kcoeff p) (i := i).
      + exact Hp.
      + exact Hrow.
    - now apply IH.
  Qed.

  Lemma seed_rows_scale_zero : forall xs total index rows,
    Forall (fun r => kscale r = 0%Z) (seed_rows xs total index rows).
  Proof.
    intros xs total index rows. revert index.
    induction rows as [|p rows IH]; intro index; [constructor |].
    cbn [seed_rows]. destruct (lrel p); [constructor |]; auto.
  Qed.

  Lemma bareiss_scale_zero : forall cols previous rs,
    Forall (fun r => kscale r = 0%Z) rs ->
    Forall (fun r => kscale r = 0%Z) (karr_bareiss cols previous rs).
  Proof.
    intro cols. induction cols as [|cols IH]; intros previous rs Hrows;
      [exact Hrows |].
    cbn [karr_bareiss]. destruct (karr_pivot rs) as [[p rest] |] eqn:Hpivot.
    - destruct (karr_pivot_some _ _ _ Hpivot) as [_ Hperm].
      assert (Hordered : Forall (fun r => kscale r = 0%Z) (p :: rest)).
      { eapply Permutation_Forall; [exact Hperm |exact Hrows]. }
      inversion Hordered as [|p' rest' Hp Hrest]; subst p' rest'.
      constructor; [exact Hp |]. apply Forall_forall. intros r Hin.
      apply in_map_iff in Hin as [s [Hsame Hin]]. subst r.
      change (kscale s = 0%Z).
      assert (Hreduced : Forall (fun r => kscale r = 0%Z)
        (map (fun r => karr_tail (karr_reduce previous (karr_head p)
          (karr_head r) p r)) rest)).
      { apply Forall_forall. intros t Ht.
        apply in_map_iff in Ht as [q [Hsame Hq]]. subst t.
        change (kscale (karr_reduce previous (karr_head p) (karr_head q) p q) = 0%Z).
        apply reduce_scale_zero; [exact Hp |].
        now apply (proj1 (Forall_forall _ _) Hrest). }
      exact (proj1 (Forall_forall _ _) (IH _ _ Hreduced) s Hin).
    - apply Forall_forall. intros r Hin.
      apply in_map_iff in Hin as [s [Hsame Hin]]. subst r.
      change (kscale s = 0%Z).
      assert (Htails : Forall (fun r => kscale r = 0%Z) (map karr_tail rs)).
      { apply Forall_forall. intros t Ht.
        apply in_map_iff in Ht as [q [Hsame Hq]]. subst t.
        change (kscale q = 0%Z).
        exact (proj1 (Forall_forall _ _) Hrows q Hq). }
      exact (proj1 (Forall_forall _ _) (IH _ _ Htails) s Hin).
  Qed.

  Lemma row_tracks_restore_map : forall P xs target offset rs,
    Forall (row_tracks P xs target (S offset)) rs ->
    Forall (row_tracks P xs target offset) (map karr_restore rs).
  Proof.
    intros P xs target offset rs Htracks. apply Forall_forall. intros r Hin.
    apply in_map_iff in Hin as [s [Hsame Hin]]. subst r. apply row_tracks_restore.
    now apply (proj1 (Forall_forall _ _) Htracks).
  Qed.

  Lemma bareiss_tracks : forall cols P xs target offset previous rs,
    offset + cols <= length xs -> Forall (row_tracks P xs target offset) rs ->
    Forall (row_tracks P xs target offset) (karr_bareiss cols previous rs).
  Proof.
    intro cols. induction cols as [|cols IH];
      intros P xs target offset previous rs Hroom Hrows; [exact Hrows |].
    cbn [karr_bareiss]. destruct (karr_pivot rs) as [[p rest] |] eqn:Hpivot.
    - destruct (karr_pivot_some _ _ _ Hpivot) as [_ Hperm].
      assert (Hordered : Forall (row_tracks P xs target offset) (p :: rest)).
      { eapply Permutation_Forall; [exact Hperm |exact Hrows]. }
      inversion Hordered as [|p' rest' Hp Hrest]; subst p' rest'.
      constructor; [exact Hp |]. apply row_tracks_restore_map. apply IH; [lia |].
      apply Forall_forall. intros r Hin.
      apply in_map_iff in Hin as [s [Hsame Hin]]. subst r.
      apply row_tracks_tail_head; [|lia |apply karr_reduce_head_zero].
      apply row_tracks_reduce; [exact Hp |].
      now apply (proj1 (Forall_forall _ _) Hrest).
    - apply row_tracks_restore_map. apply IH; [lia |].
      pose proof (karr_pivot_none _ Hpivot) as Hheads.
      apply Forall_forall. intros r Hin.
      apply in_map_iff in Hin as [s [Hsame Hin]]. subst r.
      apply row_tracks_tail_head; [|lia |].
      + now apply (proj1 (Forall_forall _ _) Hrows).
      + now apply (proj1 (Forall_forall _ _) Hheads).
  Qed.

  Lemma equality_basis_tracks : forall P xs target,
    Forall (row_tracks P xs target 0) (equality_basis xs P).
  Proof.
    intros P xs target. unfold equality_basis. apply bareiss_tracks; [lia |].
    apply seed_rows_tracks.
  Qed.

  Lemma equality_basis_scale_zero : forall P xs,
    Forall (fun r => kscale r = 0%Z) (equality_basis xs P).
  Proof.
    intros P xs. unfold equality_basis. apply bareiss_scale_zero. apply seed_rows_scale_zero.
  Qed.

  Lemma reduced_target_tracks : forall P xs target,
    row_tracks P xs target 0
      (karr_target (equality_basis xs P) 1
        (KRow (dense xs target) (rhs target) (repeat 0%Z (length P)) 1)).
  Proof.
    intros P xs target. apply target_tracks; [apply equality_basis_tracks |].
    apply target_initial_tracks.
  Qed.

  Lemma reduced_target_scale_nonzero : forall P xs target,
    kscale (karr_target (equality_basis xs P) 1
      (KRow (dense xs target) (rhs target) (repeat 0%Z (length P)) 1)) <> 0%Z.
  Proof.
    intros P xs target. apply target_scale_nonzero; [apply equality_basis_scale_zero |].
    discriminate.
  Qed.

  (** Passing the producer's residual guard is sufficient for every lawful checker. *)
  Lemma target_certificate_complete : forall P target k,
    target_certificate P target = Some k -> C.check_entails P target k = true.
  Proof.
    intros P target k Hcert. unfold target_certificate in Hcert.
    set (xs := variables (target :: P)) in *.
    set (r := karr_target (equality_basis xs P) 1
      (KRow (dense xs target) (rhs target) (repeat 0%Z (length P)) 1)) in *.
    set (sign := if (kscale r <? 0)%Z then (-1)%Z else 1%Z) in *.
    destruct (karr_zero r && negb (Z.eqb (kscale r) 0) &&
      match lrel target with
      | REq => Z.eqb (kright r) 0
      | RLe => (0 <=? sign * kright r)%Z
      end) eqn:Hguard; [|discriminate].
    injection Hcert as Hsame. subst k.
    apply andb_true_iff in Hguard as [Hleft Hright].
    apply andb_true_iff in Hleft as [Hzero Hscale].
    apply negb_true_iff, Z.eqb_neq in Hscale.
    apply row_tracks_check_entails with (xs := xs).
    - apply reduced_target_tracks.
    - intros s Hs x z Hin. apply variables_contains with (r := s) (z := z);
        assumption.
    - exact Hzero.
    - exact Hscale.
    - destruct (lrel target); [now apply Z.eqb_eq |now apply Z.leb_le].
  Qed.

  Lemma entails_of_target_certificate : forall P target k,
    target_certificate P target = Some k -> entails P target = true.
  Proof.
    intros P target k Htarget. unfold entails. apply orb_true_iff. right.
    unfold entail_cert. destruct (contradiction P) as [ms |] eqn:Hempty.
    - assert (Hcheck : C.check_entails P target (Cert ms 1 false) = true).
      { apply C.check_entails_empty. now apply contradiction_checked in Hempty. }
      now rewrite Hcheck.
    - rewrite Htarget, (target_certificate_complete _ _ _ Htarget). reflexivity.
  Qed.

  Lemma empty_certificate_accepts_row : forall P rs r,
    In r rs -> karr_zero r = true -> kright r <> 0%Z ->
    C.check_empty P (kweight r) = true ->
    exists ms, empty_certificate P rs = Some ms.
  Proof.
    intros P rs. induction rs as [|p rs IH]; intros r Hin Hzero Hnonzero Hcheck;
      [contradiction |].
    cbn [empty_certificate].
    destruct (karr_zero p && negb (Z.eqb (kright p) 0) &&
      C.check_empty P (kweight p)) eqn:Hp.
    - exists (kweight p). reflexivity.
    - destruct Hin as [Hsame | Hin].
      + subst p. apply Z.eqb_neq in Hnonzero.
        rewrite Hzero, Hnonzero, Hcheck in Hp. discriminate.
      + now apply IH with (r := r).
  Qed.

  Lemma contradiction_of_zero_row : forall P r,
    In r (equality_basis (variables P) P) -> karr_zero r = true -> kright r <> 0%Z ->
    exists ms, contradiction P = Some ms.
  Proof.
    intros P r Hin Hzero Hnonzero. unfold contradiction.
    apply empty_certificate_accepts_row with (r := r); try assumption.
    apply row_tracks_check_empty with (xs := variables P)
      (target := LCons X.t [] REq 0%Z); try assumption.
    - now apply (proj1 (Forall_forall _ _) (equality_basis_tracks P (variables P)
        (LCons X.t [] REq 0%Z))).
    - intros s Hs x z Hterm. destruct Hs as [Hsame | Hs].
      + subst s. contradiction.
      + now apply variables_contains with (r := s) (z := z).
    - now apply (proj1 (Forall_forall _ _) (equality_basis_scale_zero P (variables P))).
  Qed.

  Lemma contradiction_none_no_false_row : forall P r,
    contradiction P = None -> In r (equality_basis (variables P) P) ->
    karr_zero r = true -> kright r = 0%Z.
  Proof.
    intros P r Hnone Hin Hzero. destruct (Z.eq_dec (kright r) 0) as [Hz | Hnz];
      [exact Hz |].
    destruct (contradiction_of_zero_row _ _ Hin Hzero Hnz) as [ms Hsome].
    rewrite Hnone in Hsome. discriminate.
  Qed.

  Lemma dense_normalize_row : forall xs r,
    dense xs (normalize_row r) = dense xs r.
  Proof.
    intros xs r. unfold dense. cbn [normalize_row lhs].
    apply map_ext. intro x. apply normalize_coef_coefficient.
  Qed.

  (** Seed extraction keeps precisely the equality models of the source rows. *)
  Lemma seed_rows_models : forall xs total rows index qs,
    Forall (karr_models qs) (seed_rows xs total index rows) <->
      Forall (fun r => lrel r = REq ->
        (karr_eval qs (dense xs r) == inject_Z (rhs r))%Q) rows.
  Proof.
    intros xs total rows. induction rows as [|p rows IH]; intros index qs.
    - split; intro H; constructor.
    - cbn [seed_rows]. destruct (lrel p) eqn:Hrel.
      + rewrite !Forall_cons_iff, IH. split; intros [Hp Hrows]; split.
        * intros _. exact Hp.
        * exact Hrows.
        * now apply Hp.
        * exact Hrows.
      + rewrite Forall_cons_iff, IH. split.
        * intro Hrows. split; [|exact Hrows]. intro Hfalse. congruence.
        * intros [_ Hrows]. exact Hrows.
  Qed.

  Lemma seed_rows_width : forall xs total index rows,
    Forall (fun r => length (kcoeff r) = length xs) (seed_rows xs total index rows).
  Proof.
    intros xs total index rows. revert index.
    induction rows as [|p rows IH]; intro index; [constructor |].
    cbn [seed_rows]. destruct (lrel p); [constructor |]; auto.
    unfold dense. cbn [kcoeff]. apply length_map.
  Qed.

  Lemma dense_equality_models_Q : forall xs r v,
    lrel r = REq -> NoDup xs -> (forall x z, In (x, z) (lhs r) -> In x xs) ->
    ((karr_eval (map v xs) (dense xs r) == inject_Z (rhs r))%Q <-> satQ v r).
  Proof.
    intros xs r v Hrel Hunique Hsupport. unfold satQ. rewrite Hrel.
    change ((karr_eval (map v xs) (dense xs r) == inject_Z (rhs r))%Q <->
      (karr_eval_coef_Q v (lhs r) == inject_Z (rhs r))%Q).
    now setoid_rewrite (dense_eval_Q xs r v Hunique Hsupport).
  Qed.

  Lemma seed_rows_models_Q : forall P xs v total index,
    NoDup xs -> (forall r, In r P -> forall x z, In (x, z) (lhs r) -> In x xs) ->
    (Forall (karr_models (map v xs))
      (seed_rows xs total index (map normalize_row P)) <->
      Forall (fun r => lrel r = REq -> satQ v r) P).
  Proof.
    intros P xs v total index Hunique Hsupport.
    rewrite seed_rows_models, Forall_map. split; intro Hmodels;
      apply Forall_forall; intros r Hin Hrel.
    - pose proof (proj1 (Forall_forall _ _) Hmodels r Hin Hrel) as Hmodel.
      rewrite dense_normalize_row in Hmodel. cbn [normalize_row rhs] in Hmodel.
      apply (proj1 (dense_equality_models_Q xs r v Hrel Hunique (Hsupport r Hin))).
      exact Hmodel.
    - change (lrel r = REq) in Hrel.
      pose proof (proj1 (Forall_forall _ _) Hmodels r Hin Hrel) as Hmodel.
      rewrite dense_normalize_row. cbn [normalize_row rhs].
      apply (proj2 (dense_equality_models_Q xs r v Hrel Hunique (Hsupport r Hin))).
      exact Hmodel.
  Qed.

  Lemma equality_basis_models_Q : forall P xs v,
    NoDup xs -> (forall r, In r P -> forall x z, In (x, z) (lhs r) -> In x xs) ->
    (Forall (karr_models (map v xs)) (equality_basis xs P) <->
      Forall (fun r => lrel r = REq -> satQ v r) P).
  Proof.
    intros P xs v Hunique Hsupport. unfold equality_basis.
    assert (Hlength : length (map v xs) = length xs) by apply length_map.
    rewrite (karr_bareiss_models (length xs) 1
      (seed_rows xs (length P) 0 (map normalize_row P)) (map v xs) Hlength
      (seed_rows_width xs (length P) 0 (map normalize_row P))).
    now apply seed_rows_models_Q.
  Qed.

  Lemma coordinate_basis_models_Q : forall P xs qs,
    NoDup xs -> length xs = length qs ->
    (forall r, In r P -> forall x z, In (x, z) (lhs r) -> In x xs) ->
    (Forall (karr_models qs) (equality_basis xs P) <->
      Forall (fun r => lrel r = REq -> satQ (coordinate_store xs qs) r) P).
  Proof.
    intros P xs qs Hunique Hlength Hsupport.
    rewrite <- (coordinate_store_values xs qs Hunique Hlength) at 1.
    now apply equality_basis_models_Q.
  Qed.

  (** Equality-derived certificates retain zero weights for every source inequality. *)
  Definition equality_certificate (P : list (lcons X.t)) (c : lcons X.t)
      (ms : list Z) (sc : Z) : Prop :=
    equality_weights P ms /\ (0 < sc)%Z /\
    (forall x, C.comb_coef P ms x = (sc * C.coef_of x (lhs c))%Z) /\
    match lrel c with
    | REq => C.comb_rhs P ms = (sc * rhs c)%Z
    | RLe => (C.comb_rhs P ms <= sc * rhs c)%Z
    end.

  Lemma equality_certificate_checked : forall P c ms sc,
    equality_certificate P c ms sc -> C.check_entails P c (Cert ms sc false) = true.
  Proof.
    intros P c ms sc [Hweights [Hpositive [Hcoeff Hrhs]]].
    apply C.check_entails_complete.
    - now apply equality_weights_admissible.
    - exact Hpositive.
    - exact Hcoeff.
    - destruct (lrel c); [split; [now apply equality_weights_comb_eq |] |]; exact Hrhs.
  Qed.

  (** This proof-only source erases constraints ignored by equality elimination. *)
  Definition equality_source (P : list (lcons X.t)) : list (lcons X.t) :=
    map (fun r => match lrel r with REq => r | RLe => LCons X.t [] REq 0%Z end) P.

  Lemma equality_source_weights : forall P ms,
    equality_weights P ms -> equality_weights (equality_source P) ms.
  Proof.
    intros P ms Hweights. induction Hweights as [|p m P ms Hhead Htail IH].
    - constructor.
    - unfold equality_source in *. cbn [map]. constructor; [|exact IH].
      destruct (lrel p) eqn:Hrel; cbn [lrel]; intro Hfalse; congruence.
  Qed.

  Lemma equality_source_sum : forall P ms entry,
    equality_weights P ms -> row_sum (equality_source P) ms entry = row_sum P ms entry.
  Proof.
    intros P ms entry Hweights. induction Hweights as [|p m P ms Hhead Htail IH].
    - reflexivity.
    - change ((m * entry (match lrel p with REq => p | RLe => LCons X.t [] REq 0%Z end) +
        row_sum (equality_source P) ms entry)%Z =
        (m * entry p + row_sum P ms entry)%Z).
      rewrite IH. destruct (lrel p) eqn:Hrel; [reflexivity |].
      rewrite (Hhead eq_refl). ring.
  Qed.

  Lemma equality_source_coef : forall P ms x,
    equality_weights P ms -> C.comb_coef (equality_source P) ms x = C.comb_coef P ms x.
  Proof.
    intros P ms x Hweights.
    change (row_sum (equality_source P) ms (fun r => C.coef_of x (lhs r)) =
      row_sum P ms (fun r => C.coef_of x (lhs r))).
    exact (equality_source_sum P ms (fun r => C.coef_of x (lhs r)) Hweights).
  Qed.

  Lemma equality_source_rhs : forall P ms,
    equality_weights P ms -> C.comb_rhs (equality_source P) ms = C.comb_rhs P ms.
  Proof.
    intros P ms Hweights.
    change (row_sum (equality_source P) ms rhs = row_sum P ms rhs).
    exact (equality_source_sum P ms rhs Hweights).
  Qed.

  Lemma equality_source_models_Q : forall P v,
    Forall (fun r => lrel r = REq -> satQ v r) P -> Forall (satQ v) (equality_source P).
  Proof.
    intros P v Hmodels. unfold equality_source. rewrite Forall_map.
    apply Forall_forall. intros r Hin.
    destruct (lrel r) eqn:Hrel.
    - now apply (proj1 (Forall_forall _ _) Hmodels r Hin).
    - reflexivity.
  Qed.

  Lemma equality_certificate_sound_Q : forall P c ms sc,
    equality_certificate P c ms sc -> forall v,
    Forall (fun r => lrel r = REq -> satQ v r) P -> satQ v c.
  Proof.
    intros P c ms sc [Hweights [Hpositive [Hcoeff Hrhs]]] v Hmodels.
    apply (C.check_entails_sound_Q (equality_source P) c (Cert ms sc false)).
    - apply equality_certificate_checked. split; [now apply equality_source_weights |].
      split; [exact Hpositive |]. split.
      + intro x. rewrite equality_source_coef by exact Hweights. apply Hcoeff.
      + rewrite equality_source_rhs by exact Hweights. exact Hrhs.
    - reflexivity.
    - now apply equality_source_models_Q.
  Qed.

  Lemma equality_empty_sound_Q : forall P ms,
    equality_weights P ms -> (forall x, C.comb_coef P ms x = 0%Z) ->
    C.comb_rhs P ms <> 0%Z -> forall v,
    ~ Forall (fun r => lrel r = REq -> satQ v r) P.
  Proof.
    intros P ms Hweights Hcoeff Hrhs v Hmodels.
    assert (Hempty : C.check_empty (equality_source P) ms = true).
    { apply C.check_empty_complete.
      - apply equality_weights_admissible. now apply equality_source_weights.
      - intro x. rewrite equality_source_coef by exact Hweights. apply Hcoeff.
      - right. split.
        + apply equality_weights_comb_eq. now apply equality_source_weights.
        + now rewrite equality_source_rhs by exact Hweights. }
    pose proof (C.check_entails_empty (equality_source P) (LCons X.t [] REq 1%Z)
      (Cert ms 1 false) Hempty) as Hchecked.
    pose proof (C.check_entails_sound_Q (equality_source P) (LCons X.t [] REq 1%Z)
      (Cert ms 1 false) Hchecked eq_refl v (equality_source_models_Q P v Hmodels)) as Hfalse.
    cbn [satQ lhs rhs lrel fold_right inject_Z Qeq] in Hfalse. discriminate.
  Qed.

  Lemma row_tracks_equality_certificate : forall P xs target r,
    row_tracks P xs target 0 r ->
    (forall s, In s (target :: P) ->
      forall x z, In (x, z) (lhs s) -> In x xs) ->
    karr_zero r = true -> kscale r <> 0%Z ->
    (match lrel target with
     | REq => kright r = 0%Z
     | RLe => (0 <= (if (kscale r <? 0)%Z then -1 else 1) * kright r)%Z
     end) ->
    equality_certificate P target
      (map (fun z => (-(if (kscale r <? 0)%Z then -1 else 1) * z)%Z) (kweight r))
      (Z.abs (kscale r)).
  Proof.
    intros P xs target r Htracks Hsupport Hzero Hnonzero Hright.
    pose proof (row_tracks_zero_coeff P xs target r Htracks Hsupport Hzero) as Hcoeff.
    destruct Htracks as [Hweights [_ Hrhs]].
    set (sign := if (kscale r <? 0)%Z then (-1)%Z else 1%Z) in *.
    assert (Hsign : (sign * kscale r = Z.abs (kscale r))%Z).
    { apply coefficient_sign_abs. }
    split; [now apply equality_weights_scale |].
    split; [destruct (kscale r); cbn in *; lia |]. split.
    - intro x. rewrite comb_coef_scale. specialize (Hcoeff x).
      change ((-sign * C.comb_coef P (kweight r) x)%Z =
        (Z.abs (kscale r) * coefficient x (lhs target))%Z).
      nia.
    - destruct (lrel target); rewrite comb_rhs_scale; nia.
  Qed.

  Lemma target_certificate_equality : forall P target k,
    target_certificate P target = Some k ->
    equality_certificate P target (mults k) (scale k).
  Proof.
    intros P target k Hcert. unfold target_certificate in Hcert.
    set (xs := variables (target :: P)) in *.
    set (r := karr_target (equality_basis xs P) 1
      (KRow (dense xs target) (rhs target) (repeat 0%Z (length P)) 1)) in *.
    set (sign := if (kscale r <? 0)%Z then (-1)%Z else 1%Z) in *.
    destruct (karr_zero r && negb (Z.eqb (kscale r) 0) &&
      match lrel target with
      | REq => Z.eqb (kright r) 0
      | RLe => (0 <=? sign * kright r)%Z
      end) eqn:Hguard; [|discriminate].
    injection Hcert as Hsame. subst k.
    apply andb_true_iff in Hguard as [Hleft Hright].
    apply andb_true_iff in Hleft as [Hzero Hscale].
    apply negb_true_iff, Z.eqb_neq in Hscale.
    apply row_tracks_equality_certificate with (xs := xs).
    - apply reduced_target_tracks.
    - intros s Hs x z Hin. apply variables_contains with (r := s) (z := z); assumption.
    - exact Hzero.
    - exact Hscale.
    - destruct (lrel target); [now apply Z.eqb_eq |now apply Z.leb_le].
  Qed.

  Lemma target_certificate_sound_Q : forall P target k,
    target_certificate P target = Some k -> forall v,
    Forall (fun r => lrel r = REq -> satQ v r) P -> satQ v target.
  Proof.
    intros P target k Hcert v Hmodels.
    apply equality_certificate_sound_Q with (P := P) (ms := mults k) (sc := scale k);
      [now apply target_certificate_equality |exact Hmodels].
  Qed.

  Lemma empty_certificate_has_row : forall P rs ms,
    empty_certificate P rs = Some ms ->
    exists r, In r rs /\ karr_zero r = true /\ kright r <> 0%Z /\ kweight r = ms.
  Proof.
    intros P rs. induction rs as [|p rs IH]; intros ms Hcert; [discriminate |].
    cbn [empty_certificate] in Hcert.
    destruct (karr_zero p && negb (Z.eqb (kright p) 0) &&
      C.check_empty P (kweight p)) eqn:Hcheck.
    - injection Hcert as Hsame. subst ms. exists p. split; [now left |].
      apply andb_true_iff in Hcheck as [Hleft _].
      apply andb_true_iff in Hleft as [Hzero Hright].
      apply negb_true_iff, Z.eqb_neq in Hright. auto.
    - destruct (IH _ Hcert) as [r [Hin Hrow]]. exists r. split; [now right |exact Hrow].
  Qed.

  Lemma contradiction_sound_Q : forall P ms,
    contradiction P = Some ms -> forall v,
    ~ Forall (fun r => lrel r = REq -> satQ v r) P.
  Proof.
    intros P ms Hempty v Hmodels. unfold contradiction in Hempty.
    destruct (empty_certificate_has_row _ _ _ Hempty)
      as [r [Hin [Hzero [Hright _]]]].
    pose proof (proj1 (Forall_forall _ _)
      (equality_basis_tracks P (variables P) (LCons X.t [] REq 0%Z)) r Hin) as Htracks.
    pose proof (proj1 (Forall_forall _ _)
      (equality_basis_scale_zero P (variables P)) r Hin) as Hscale.
    assert (Hsupport : forall s, In s (LCons X.t [] REq 0%Z :: P) ->
      forall x z, In (x, z) (lhs s) -> In x (variables P)).
    { intros s Hs x z Hterm. destruct Hs as [Hsame | Hs].
      - subst s. contradiction.
      - now apply variables_contains with (r := s) (z := z). }
    pose proof (row_tracks_zero_coeff P (variables P) (LCons X.t [] REq 0%Z) r
      Htracks Hsupport Hzero) as Hcoeff.
    destruct Htracks as [Hweights [_ Hrhs]].
    apply (equality_empty_sound_Q P (kweight r) Hweights) with (v := v).
    - intro x. specialize (Hcoeff x). rewrite Hscale in Hcoeff. lia.
    - rewrite Hscale in Hrhs. lia.
    - exact Hmodels.
  Qed.

  Lemma entail_cert_sound_Q : forall P target k,
    entail_cert P target = Some k -> forall v,
    Forall (fun r => lrel r = REq -> satQ v r) P -> satQ v target.
  Proof.
    intros P target k Hcert v Hmodels. unfold entail_cert in Hcert.
    destruct (contradiction P) as [ms |] eqn:Hempty.
    - exfalso. exact (contradiction_sound_Q P ms Hempty v Hmodels).
    - destruct (target_certificate P target) as [candidate |] eqn:Htarget;
        [|discriminate].
      now apply target_certificate_sound_Q with (P := P) (k := candidate).
  Qed.

  Lemma entails_eq_sound_Q : forall P r,
    entails P r = true -> lrel r = REq -> forall v,
    Forall (fun s => lrel s = REq -> satQ v s) P -> satQ v r.
  Proof.
    intros P r Hentails Hrel v Hmodels. unfold entails in Hentails.
    apply orb_true_iff in Hentails as [Hliteral | Hcert].
    - apply existsb_exists in Hliteral as [s [Hin Hsame]].
      apply row_eqb_sound in Hsame. subst s.
      now apply (proj1 (Forall_forall _ _) Hmodels r Hin).
    - destruct (entail_cert P r) as [k |] eqn:Hsome; [|discriminate].
      now apply entail_cert_sound_Q with (P := P) (k := k).
  Qed.

  Lemma leb_eq_sound_Q : forall P R,
    leb (Reached P) (Reached R) = true -> forall v,
    Forall (fun r => lrel r = REq -> satQ v r) P ->
    Forall (fun r => lrel r = REq -> satQ v r) R.
  Proof.
    intros P R Hle v Hmodels. unfold leb in Hle.
    destruct (contradiction P) as [ms |] eqn:Hempty.
    - exfalso. exact (contradiction_sound_Q P ms Hempty v Hmodels).
    - apply Forall_forall. intros r Hin Hrel. apply entails_eq_sound_Q with (P := P).
      + now apply (proj1 (forallb_forall _ _) Hle).
      + exact Hrel.
      + exact Hmodels.
  Qed.

  (** The dense basis always has the structural echelon form proved above. *)
  Lemma equality_basis_echelon : forall P xs,
    karr_echelon (length xs) (equality_basis xs P).
  Proof.
    intros P xs. unfold equality_basis. apply karr_bareiss_echelon. apply seed_rows_width.
  Qed.

  Lemma equality_basis_width : forall P xs,
    Forall (fun r => length (kcoeff r) = length xs) (equality_basis xs P).
  Proof.
    intros P xs. apply karr_echelon_width. apply equality_basis_echelon.
  Qed.

  (** Failure to produce a contradiction supplies an actual rational equality model. *)
  Lemma contradiction_none_model_Q : forall P, contradiction P = None ->
    exists v : X.t -> Q, Forall (fun r => lrel r = REq -> satQ v r) P.
  Proof.
    intros P Hnone. set (xs := variables P).
    assert (Hzero : karr_zero_right (equality_basis xs P)).
    { apply Forall_forall. intros r Hin Hrowzero.
      exact (contradiction_none_no_false_row P r Hnone Hin Hrowzero). }
    destruct (karr_echelon_model _ _ (equality_basis_echelon P xs) Hzero)
      as [qs [Hlength Hmodels]].
    exists (coordinate_store xs qs).
    assert (Hsupport : forall r, In r P -> forall x z, In (x, z) (lhs r) -> In x xs).
    { intros r Hin x z Hterm. now apply variables_contains with (r := r) (z := z). }
    apply (proj1 (coordinate_basis_models_Q P xs qs (variables_nodup P)
      (eq_sym Hlength) Hsupport)). exact Hmodels.
  Qed.

  (** A modeled basis has no false constant row, regardless of the chosen variable list. *)
  Lemma equality_basis_zero_right : forall P xs v,
    NoDup xs ->
    (forall r, In r P -> forall x z, In (x, z) (lhs r) -> In x xs) ->
    Forall (fun r => lrel r = REq -> satQ v r) P ->
    karr_zero_right (equality_basis xs P).
  Proof.
    intros P xs v Hunique Hsupport Hmodels.
    pose proof (proj2 (equality_basis_models_Q P xs v Hunique Hsupport) Hmodels) as Hbasis.
    apply Forall_forall. intros r Hin Hzero.
    apply karr_zero_model_right with (qs := map v xs); [|exact Hzero].
    now apply (proj1 (Forall_forall _ _) Hbasis).
  Qed.

  (** The tracked target scale relates the residual to the original target over every model. *)
  Lemma reduced_target_defect_Q : forall P xs target qs,
    Forall (karr_models qs) (equality_basis xs P) ->
    karr_scaled_defect qs
      (KRow (dense xs target) (rhs target) (repeat 0%Z (length P)) 1)
      (karr_target (equality_basis xs P) 1
        (KRow (dense xs target) (rhs target) (repeat 0%Z (length P)) 1)).
  Proof.
    intros P xs target qs Hmodels.
    apply karr_target_scaled_defect with (n := length xs).
    - exact Hmodels.
    - apply equality_basis_scale_zero.
    - apply equality_basis_width.
    - cbn [kcoeff]. unfold dense. apply length_map.
    - unfold karr_scaled_defect. cbn [kscale]. ring.
  Qed.

  (** Dense and sparse satisfaction agree for both equality and inequality targets. *)
  Lemma dense_satQ : forall xs r v,
    NoDup xs -> (forall x z, In (x, z) (lhs r) -> In x xs) ->
    (satQ v r <->
      match lrel r with
      | REq => (karr_eval (map v xs) (dense xs r) == inject_Z (rhs r))%Q
      | RLe => (karr_eval (map v xs) (dense xs r) <= inject_Z (rhs r))%Q
      end).
  Proof.
    intros xs r v Hunique Hsupport.
    pose proof (dense_eval_Q xs r v Hunique Hsupport) as Heval.
    unfold satQ. destruct (lrel r).
    - change ((karr_eval_coef_Q v (lhs r) == inject_Z (rhs r))%Q <->
        (karr_eval (map v xs) (dense xs r) == inject_Z (rhs r))%Q).
      now setoid_rewrite Heval.
    - change ((karr_eval_coef_Q v (lhs r) <= inject_Z (rhs r))%Q <->
        (karr_eval (map v xs) (dense xs r) <= inject_Z (rhs r))%Q).
      now setoid_rewrite Heval.
  Qed.

  Lemma coordinate_satQ : forall xs qs r,
    NoDup xs -> length xs = length qs ->
    (forall x z, In (x, z) (lhs r) -> In x xs) ->
    (satQ (coordinate_store xs qs) r <->
      match lrel r with
      | REq => (karr_eval qs (dense xs r) == inject_Z (rhs r))%Q
      | RLe => (karr_eval qs (dense xs r) <= inject_Z (rhs r))%Q
      end).
  Proof.
    intros xs qs r Hunique Hlength Hsupport.
    rewrite (dense_satQ xs r (coordinate_store xs qs) Hunique Hsupport).
    now rewrite (coordinate_store_values xs qs Hunique Hlength).
  Qed.

  (** Every rational consequence of the equality rows passes the producer residual guard. *)
  Lemma target_certificate_complete_Q : forall P target,
    contradiction P = None ->
    (forall v : X.t -> Q,
      Forall (fun r => lrel r = REq -> satQ v r) P -> satQ v target) ->
    exists k, target_certificate P target = Some k.
  Proof.
    intros P target Hnone Hsemantic.
    destruct (contradiction_none_model_Q P Hnone) as [v0 Hmodel0].
    set (xs := variables (target :: P)).
    set (initial := KRow (dense xs target) (rhs target) (repeat 0%Z (length P)) 1).
    set (r := karr_target (equality_basis xs P) 1 initial).
    assert (Hunique : NoDup xs) by apply variables_nodup.
    assert (Hsupport : forall s, In s (target :: P) ->
      forall x z, In (x, z) (lhs s) -> In x xs).
    { intros s Hin x z Hterm. now apply variables_contains with (r := s) (z := z). }
    assert (Hsource : forall s, In s P ->
      forall x z, In (x, z) (lhs s) -> In x xs).
    { intros s Hin. apply Hsupport. now right. }
    assert (Htarget : forall x z, In (x, z) (lhs target) -> In x xs).
    { apply Hsupport. now left. }
    pose proof (equality_basis_echelon P xs) as Hechelon.
    pose proof (equality_basis_zero_right P xs v0 Hunique Hsource Hmodel0) as Hconsistent.
    assert (Hscale : kscale r <> 0%Z) by apply reduced_target_scale_nonzero.
    assert (HscaleQ : ~ (inject_Z (kscale r) == 0)%Q).
    { now apply karr_inject_nonzero. }
    assert (Hwidth : length (kcoeff r) = length xs).
    { apply karr_target_width with (n := length xs).
      - apply equality_basis_width.
      - cbn [initial kcoeff]. unfold dense. apply length_map. }
    assert (Hreduced : karr_reduced (equality_basis xs P) (kcoeff r)).
    { apply karr_target_reduced with (n := length xs). exact Hechelon. }
    assert (Hzero : karr_zero r = true).
    { destruct (karr_zero r) eqn:Hrowzero; [reflexivity|]. exfalso.
      destruct (karr_echelon_countermodel _ _ Hechelon Hconsistent _ Hwidth Hreduced
        Hrowzero (inject_Z (kright r) + inject_Z (kscale r))%Q)
        as [qs [Hlength [Hbasis Hvalue]]].
      assert (HP : Forall (fun s => lrel s = REq -> satQ (coordinate_store xs qs) s) P).
      { apply (proj1 (coordinate_basis_models_Q P xs qs Hunique ltac:(lia) Hsource)).
        exact Hbasis. }
      pose proof (proj1 (coordinate_satQ xs qs target Hunique ltac:(lia) Htarget)
        (Hsemantic _ HP)) as Htarget_sat.
      pose proof (reduced_target_defect_Q P xs target qs Hbasis) as Hdefect.
      change (karr_eval qs (kcoeff r) - inject_Z (kright r) ==
        inject_Z (kscale r) * (karr_eval qs (dense xs target) - inject_Z (rhs target)))%Q
        in Hdefect.
      assert (Hbad : (karr_eval qs (dense xs target) - inject_Z (rhs target) == 1)%Q).
      { apply (proj1 (Qmult_inj_l _ _ (inject_Z (kscale r)) HscaleQ)).
        eapply Qeq_trans; [symmetry; exact Hdefect|].
        setoid_rewrite Hvalue. ring. }
      destruct (lrel target); nra. }
    pose proof (proj2 (equality_basis_models_Q P xs v0 Hunique Hsource) Hmodel0) as Hbasis0.
    pose proof (reduced_target_defect_Q P xs target (map v0 xs) Hbasis0) as Hdefect0.
    change (karr_eval (map v0 xs) (kcoeff r) - inject_Z (kright r) ==
      inject_Z (kscale r) * (karr_eval (map v0 xs) (dense xs target) -
        inject_Z (rhs target)))%Q in Hdefect0.
    setoid_rewrite (karr_eval_zero _ Hzero (map v0 xs)) in Hdefect0.
    pose proof (proj1 (dense_satQ xs target v0 Hunique Htarget)
      (Hsemantic v0 Hmodel0)) as Htarget_sat0.
    assert (Hright : match lrel target with
      | REq => Z.eqb (kright r) 0
      | RLe => (0 <=? (if (kscale r <? 0)%Z then -1 else 1) * kright r)%Z
      end = true).
    { destruct (lrel target).
      - setoid_rewrite Htarget_sat0 in Hdefect0.
        apply Z.eqb_eq. apply (proj1 (inject_Z_injective _ _)).
        change (inject_Z (kright r) == 0)%Q. nra.
      - apply Z.leb_le. destruct (Z.ltb (kscale r) 0) eqn:Hsign.
        + apply Z.ltb_lt in Hsign. rewrite Zlt_Qlt in Hsign.
          change (inject_Z (kscale r) < 0)%Q in Hsign.
          assert (Hnegative_scale : (0 <= - inject_Z (kscale r))%Q) by lra.
          assert (Hnegative_delta : (0 <= inject_Z (rhs target) -
            karr_eval (map v0 xs) (dense xs target))%Q) by lra.
          pose proof (Qmult_le_0_compat _ _ Hnegative_scale Hnegative_delta) as Hproduct.
          assert (Hrhs : (inject_Z (kright r) <= 0)%Q) by nra.
          change (inject_Z (kright r) <= inject_Z 0)%Q in Hrhs.
          rewrite <- Zle_Qle in Hrhs. lia.
        + apply Z.ltb_ge in Hsign.
          assert (Hpositive : (0 < kscale r)%Z) by lia.
          rewrite Zlt_Qlt in Hpositive.
          change (0 < inject_Z (kscale r))%Q in Hpositive.
          assert (Hpositive_scale : (0 <= inject_Z (kscale r))%Q) by lra.
          assert (Hnegative_delta : (0 <= inject_Z (rhs target) -
            karr_eval (map v0 xs) (dense xs target))%Q) by lra.
          pose proof (Qmult_le_0_compat _ _ Hpositive_scale Hnegative_delta) as Hproduct.
          assert (Hrhs : (0 <= inject_Z (kright r))%Q) by nra.
          change (inject_Z 0 <= inject_Z (kright r))%Q in Hrhs.
          rewrite <- Zle_Qle in Hrhs. lia. }
    unfold target_certificate. fold xs initial r.
    assert (Hscale_bool : Z.eqb (kscale r) 0 = false) by now apply Z.eqb_neq.
    rewrite Hzero, Hscale_bool, Hright. eexists. reflexivity.
  Qed.

  Lemma entails_complete_Q : forall P target,
    (forall v : X.t -> Q,
      Forall (fun r => lrel r = REq -> satQ v r) P -> satQ v target) ->
    entails P target = true.
  Proof.
    intros P target Hsemantic. destruct (contradiction P) as [ms|] eqn:Hempty.
    - unfold entails, entail_cert. rewrite Hempty.
      assert (Hchecked : C.check_entails P target (Cert ms 1 false) = true).
      { apply C.check_entails_empty. now apply contradiction_checked in Hempty. }
      rewrite Hchecked. apply orb_true_r.
    - destruct (target_certificate_complete_Q P target Hempty Hsemantic) as [k Htarget].
      now apply entails_of_target_certificate with (k := k).
  Qed.


  (** Left models use equal ordinary values and opposite homogeneous values. *)
  Definition hull_values_left (xs : list X.t) (v : X.t -> Q) : list Q :=
    (map v xs ++ [1%Q]) ++ (map v xs ++ [-1%Q]).

  (** Right models set the first coordinate block to zero. *)
  Definition hull_values_right (xs : list X.t) (v : X.t -> Q) : list Q :=
    (repeat 0%Q (length xs) ++ [0%Q]) ++ (map v xs ++ [-1%Q]).

  Lemma hull_values_left_length : forall xs v,
    length (hull_values_left xs v) = 2 * length xs + 2.
  Proof.
    intros xs v. unfold hull_values_left. rewrite !length_app, !length_map.
    cbn [length]. lia.
  Qed.

  Lemma hull_values_right_length : forall xs v,
    length (hull_values_right xs v) = 2 * length xs + 2.
  Proof.
    intros xs v. unfold hull_values_right.
    rewrite !length_app, repeat_length, length_map. cbn [length]. lia.
  Qed.

  Lemma hull_left_width : forall xs total index rows,
    Forall (fun r => length (kcoeff r) = 2 * length xs + 2)
      (hull_left xs total index rows).
  Proof.
    intros xs total index rows. revert index.
    induction rows as [|r rows IH]; intro index; [constructor|].
    cbn [hull_left]. destruct (lrel r); [constructor|]; [|apply IH|apply IH].
    cbn [kcoeff]. rewrite length_app. cbn [length].
    unfold dense. rewrite length_map, repeat_length. lia.
  Qed.

  Lemma hull_right_width : forall xs total index rows,
    Forall (fun r => length (kcoeff r) = 2 * length xs + 2)
      (hull_right xs total index rows).
  Proof.
    intros xs total index rows. revert index.
    induction rows as [|r rows IH]; intro index; [constructor|].
    cbn [hull_right]. destruct (lrel r); [constructor|]; [|apply IH|apply IH].
    cbn [kcoeff]. rewrite length_app. cbn [length]. rewrite length_app.
    unfold dense. rewrite !length_map. cbn [length]. lia.
  Qed.

  Lemma hull_left_zero_right : forall xs total index rows,
    Forall (fun r => kright r = 0%Z) (hull_left xs total index rows).
  Proof.
    intros xs total index rows. revert index.
    induction rows as [|r rows IH]; intro index; [constructor|].
    cbn [hull_left]. destruct (lrel r); [constructor|]; auto.
  Qed.

  Lemma hull_right_zero_right : forall xs total index rows,
    Forall (fun r => kright r = 0%Z) (hull_right xs total index rows).
  Proof.
    intros xs total index rows. revert index.
    induction rows as [|r rows IH]; intro index; [constructor|].
    cbn [hull_right]. destruct (lrel r); [constructor|]; auto.
  Qed.

  (** Normalizing repeated coefficients preserves rational satisfaction. *)
  Lemma normalize_row_sat_Q : forall v r,
    satQ v (normalize_row r) <-> satQ v r.
  Proof.
    intros v r. unfold satQ. cbn [normalize_row lhs lrel rhs].
    change ((match lrel r with
      | REq => (karr_eval_coef_Q v (normalize_coef (lhs r)) == inject_Z (rhs r))%Q
      | RLe => (karr_eval_coef_Q v (normalize_coef (lhs r)) <= inject_Z (rhs r))%Q
      end) <->
      match lrel r with
      | REq => (karr_eval_coef_Q v (lhs r) == inject_Z (rhs r))%Q
      | RLe => (karr_eval_coef_Q v (lhs r) <= inject_Z (rhs r))%Q
      end).
    destruct (lrel r); setoid_rewrite normalize_coef_eval_Q; reflexivity.
  Qed.

  Lemma normalize_rows_equality_models_Q : forall rows v,
    Forall (fun r => lrel r = REq -> satQ v r) rows ->
    Forall (fun r => lrel r = REq -> satQ v r) (map normalize_row rows).
  Proof.
    intros rows v Hmodels. rewrite Forall_map. apply Forall_forall.
    intros r Hin Hrel. apply normalize_row_sat_Q.
    apply (proj1 (Forall_forall _ _) Hmodels r Hin). exact Hrel.
  Qed.

  Lemma hull_left_models_left : forall xs total rows index v,
    NoDup xs ->
    (forall r, In r rows -> forall x z, In (x, z) (lhs r) -> In x xs) ->
    Forall (fun r => lrel r = REq -> satQ v r) rows ->
    Forall (karr_models (hull_values_left xs v)) (hull_left xs total index rows).
  Proof.
    intros xs total rows. induction rows as [|r rows IH];
      intros index v Hunique Hsupport Hmodels; [constructor|].
    inversion Hmodels as [|r' rows' Hmodel Htail]; subst r' rows'.
    cbn [hull_left]. destruct (lrel r) eqn:Hrel.
    - constructor.
      + assert (Heval : (karr_eval (map v xs) (dense xs r) == inject_Z (rhs r))%Q).
        { apply (proj2 (dense_equality_models_Q xs r v Hrel Hunique
            (Hsupport r (or_introl eq_refl)))). apply Hmodel. auto. }
        unfold karr_models, hull_values_left. cbn [kcoeff kright].
        assert (Hlength : length (map v xs) = length (dense xs r)).
        { unfold dense. now rewrite !length_map. }
        setoid_rewrite (karr_eval_hull_left (map v xs) (dense xs r) Hlength
          1%Q (map v xs ++ [-1%Q]) (rhs r) (S (length xs))).
        setoid_rewrite Heval. change (inject_Z (rhs r) - inject_Z (rhs r) * 1 == 0)%Q.
        ring.
      + apply IH; [exact Hunique| |exact Htail].
        intros p Hin x z Hterm. exact (Hsupport p (or_intror Hin) x z Hterm).
    - apply IH; [exact Hunique| |exact Htail].
      intros p Hin x z Hterm. exact (Hsupport p (or_intror Hin) x z Hterm).
  Qed.

  Lemma hull_left_models_right : forall xs total rows index v,
    Forall (karr_models (hull_values_right xs v)) (hull_left xs total index rows).
  Proof.
    intros xs total rows. induction rows as [|r rows IH]; intros index v;
      [constructor|].
    cbn [hull_left]. destruct (lrel r); [constructor|]; [|apply IH|apply IH].
    unfold karr_models, hull_values_right. cbn [kcoeff kright].
    assert (Hlength : length (repeat 0%Q (length xs)) = length (dense xs r)).
    { unfold dense. now rewrite repeat_length, length_map. }
    setoid_rewrite (karr_eval_hull_left (repeat 0%Q (length xs)) (dense xs r)
      Hlength 0%Q (map v xs ++ [-1%Q]) (rhs r) (S (length xs))).
    setoid_rewrite karr_eval_zero_values.
    change (0 - inject_Z (rhs r) * 0 == 0)%Q. ring.
  Qed.

  Lemma hull_right_models_left : forall xs total rows index v,
    Forall (karr_models (hull_values_left xs v)) (hull_right xs total index rows).
  Proof.
    intros xs total rows. induction rows as [|r rows IH]; intros index v;
      [constructor|].
    cbn [hull_right]. destruct (lrel r); [constructor|]; [|apply IH|apply IH].
    unfold karr_models, hull_values_left. cbn [kcoeff kright].
    assert (Hlength : length (map v xs) = length (dense xs r)).
    { unfold dense. now rewrite !length_map. }
    setoid_rewrite (karr_eval_hull_right (map v xs) (map v xs) (dense xs r)
      Hlength Hlength 1%Q (-1)%Q (rhs r)).
    change (- karr_eval (map v xs) (dense xs r) + inject_Z (rhs r) * 1 +
      karr_eval (map v xs) (dense xs r) + inject_Z (rhs r) * (-1) == 0)%Q.
    ring.
  Qed.

  Lemma hull_right_models_right : forall xs total rows index v,
    NoDup xs ->
    (forall r, In r rows -> forall x z, In (x, z) (lhs r) -> In x xs) ->
    Forall (fun r => lrel r = REq -> satQ v r) rows ->
    Forall (karr_models (hull_values_right xs v)) (hull_right xs total index rows).
  Proof.
    intros xs total rows. induction rows as [|r rows IH];
      intros index v Hunique Hsupport Hmodels; [constructor|].
    inversion Hmodels as [|r' rows' Hmodel Htail]; subst r' rows'.
    cbn [hull_right]. destruct (lrel r) eqn:Hrel.
    - constructor.
      + assert (Heval : (karr_eval (map v xs) (dense xs r) == inject_Z (rhs r))%Q).
        { apply (proj2 (dense_equality_models_Q xs r v Hrel Hunique
            (Hsupport r (or_introl eq_refl)))). apply Hmodel. auto. }
        unfold karr_models, hull_values_right. cbn [kcoeff kright].
        assert (Hleft : length (repeat 0%Q (length xs)) = length (dense xs r)).
        { unfold dense. now rewrite repeat_length, length_map. }
        assert (Hright : length (map v xs) = length (dense xs r)).
        { unfold dense. now rewrite !length_map. }
        setoid_rewrite (karr_eval_hull_right (repeat 0%Q (length xs))
          (map v xs) (dense xs r) Hleft Hright 0%Q (-1)%Q (rhs r)).
        setoid_rewrite karr_eval_zero_values. setoid_rewrite Heval.
        change (-0 + inject_Z (rhs r) * 0 + inject_Z (rhs r) +
          inject_Z (rhs r) * (-1) == 0)%Q. ring.
      + apply IH; [exact Hunique| |exact Htail].
        intros p Hin x z Hterm. exact (Hsupport p (or_intror Hin) x z Hterm).
    - apply IH; [exact Hunique| |exact Htail].
      intros p Hin x z Hterm. exact (Hsupport p (or_intror Hin) x z Hterm).
  Qed.

  Lemma hull_seed_width : forall xs total left_index right_index P Q,
    Forall (fun r => length (kcoeff r) = 2 * length xs + 2)
      (hull_left xs total left_index P ++ hull_right xs total right_index Q).
  Proof.
    intros xs total left_index right_index P Q. apply Forall_app. split.
    - apply hull_left_width.
    - apply hull_right_width.
  Qed.

  Lemma hull_seed_zero_right : forall xs total left_index right_index P Q,
    Forall (fun r => kright r = 0%Z)
      (hull_left xs total left_index P ++ hull_right xs total right_index Q).
  Proof.
    intros xs total left_index right_index P Q. apply Forall_app. split.
    - apply hull_left_zero_right.
    - apply hull_right_zero_right.
  Qed.

  (** Every equality model of the left input extends to a model of all hull seeds. *)
  Lemma hull_seed_models_left : forall A B v,
    let P := map normalize_row A in
    let Q := map normalize_row B in
    let xs := variables (P ++ Q) in
    Forall (fun r => lrel r = REq -> satQ v r) A ->
    Forall (karr_models (hull_values_left xs v))
      (hull_left xs (length A + length B) 0 P ++
        hull_right xs (length A + length B) (length A) Q).
  Proof.
    intros A B v P Q xs Hmodels. apply Forall_app. split.
    - apply hull_left_models_left.
      + apply variables_nodup.
      + intros r Hin x z Hterm. apply variables_contains with (r := r) (z := z).
        * apply in_or_app. left. exact Hin.
        * exact Hterm.
      + apply normalize_rows_equality_models_Q. exact Hmodels.
    - apply hull_right_models_left.
  Qed.

  (** Every equality model of the right input extends to a model of all hull seeds. *)
  Lemma hull_seed_models_right : forall A B v,
    let P := map normalize_row A in
    let Q := map normalize_row B in
    let xs := variables (P ++ Q) in
    Forall (fun r => lrel r = REq -> satQ v r) B ->
    Forall (karr_models (hull_values_right xs v))
      (hull_left xs (length A + length B) 0 P ++
        hull_right xs (length A + length B) (length A) Q).
  Proof.
    intros A B v P Q xs Hmodels. apply Forall_app. split.
    - apply hull_left_models_right.
    - apply hull_right_models_right.
      + apply variables_nodup.
      + intros r Hin x z Hterm. apply variables_contains with (r := r) (z := z).
        * apply in_or_app. right. exact Hin.
        * exact Hterm.
      + apply normalize_rows_equality_models_Q. exact Hmodels.
  Qed.

  Lemma hull_basis_models_left : forall A B v,
    let P := map normalize_row A in
    let Q := map normalize_row B in
    let xs := variables (P ++ Q) in
    Forall (fun r => lrel r = REq -> satQ v r) A ->
    Forall (karr_models (hull_values_left xs v))
      (karr_bareiss (2 * length xs + 2) 1
        (hull_left xs (length A + length B) 0 P ++
          hull_right xs (length A + length B) (length A) Q)).
  Proof.
    intros A B v P Q xs Hmodels. apply (proj2 (karr_bareiss_models
      (2 * length xs + 2) 1 _ (hull_values_left xs v)
      (hull_values_left_length xs v) (hull_seed_width xs _ _ _ P Q))).
    exact (hull_seed_models_left A B v Hmodels).
  Qed.

  Lemma hull_basis_models_right : forall A B v,
    let P := map normalize_row A in
    let Q := map normalize_row B in
    let xs := variables (P ++ Q) in
    Forall (fun r => lrel r = REq -> satQ v r) B ->
    Forall (karr_models (hull_values_right xs v))
      (karr_bareiss (2 * length xs + 2) 1
        (hull_left xs (length A + length B) 0 P ++
          hull_right xs (length A + length B) (length A) Q)).
  Proof.
    intros A B v P Q xs Hmodels. apply (proj2 (karr_bareiss_models
      (2 * length xs + 2) 1 _ (hull_values_right xs v)
      (hull_values_right_length xs v) (hull_seed_width xs _ _ _ P Q))).
    exact (hull_seed_models_right A B v Hmodels).
  Qed.

  Lemma hull_basis_width : forall A B,
    let P := map normalize_row A in
    let Q := map normalize_row B in
    let xs := variables (P ++ Q) in
    Forall (fun r => length (kcoeff r) = 2 * length xs + 2)
      (karr_bareiss (2 * length xs + 2) 1
        (hull_left xs (length A + length B) 0 P ++
          hull_right xs (length A + length B) (length A) Q)).
  Proof.
    intros A B P Q xs. apply karr_echelon_width, karr_bareiss_echelon.
    apply hull_seed_width.
  Qed.

  Lemma hull_basis_zero_right : forall A B,
    let P := map normalize_row A in
    let Q := map normalize_row B in
    let xs := variables (P ++ Q) in
    Forall (fun r => kright r = 0%Z)
      (karr_bareiss (2 * length xs + 2) 1
        (hull_left xs (length A + length B) 0 P ++
          hull_right xs (length A + length B) (length A) Q)).
  Proof.
    intros A B P Q xs. apply karr_bareiss_zero_right.
    - apply hull_seed_width.
    - apply hull_seed_zero_right.
  Qed.

  Lemma hull_sparse_eval_Q : forall xs zs v,
    (karr_eval (map v xs) zs == karr_eval_coef_Q v (sparse xs zs))%Q.
  Proof.
    intros xs zs v. unfold sparse. setoid_rewrite eval_coef_nonzero_Q.
    apply dense_combine_eval_Q.
  Qed.

  (** A successful hull output is satisfied by every lifted model with its zero auxiliaries. *)
  Lemma checked_hull_row_sound_Q : forall xs a b r c aux v,
    length aux = S (length xs) -> length (kcoeff r) = 2 * length xs + 2 ->
    kright r = 0%Z ->
    karr_models (aux ++ (map v xs ++ [(-1)%Q])) r ->
    checked_hull_row xs a b r = Some c -> satQ v c.
  Proof.
    intros xs a b r c aux v Haux Hwidth Hright Hmodel Hrow.
    unfold checked_hull_row in Hrow.
    set (zs := skipn (S (length xs)) (kcoeff r)) in *.
    remember (LCons X.t (sparse xs zs) REq (karr_nth (length xs) zs)) as output.
    destruct (forallb (Z.eqb 0) (firstn (S (length xs)) (kcoeff r)) &&
      negb (forallb (Z.eqb 0) zs) &&
      C.check_entails a output (Cert (firstn (length a) (kweight r)) 1 false) &&
      C.check_entails b output (Cert (skipn (length a) (kweight r)) 1 false))
      eqn:Hchecked; [|discriminate].
    injection Hrow as Hsame. subst c.
    apply andb_true_iff in Hchecked as [Hchecked _].
    apply andb_true_iff in Hchecked as [Hchecked _].
    apply andb_true_iff in Hchecked as [Hzero _].
    assert (Haux_width : length aux <= length (kcoeff r)) by lia.
    assert (Haux_zero : forallb (Z.eqb 0) (firstn (length aux) (kcoeff r)) = true).
    { now rewrite Haux. }
    pose proof (karr_eval_zero_prefix aux (map v xs ++ [(-1)%Q])
      (kcoeff r) Haux_width Haux_zero) as Hsplit.
    rewrite Haux in Hsplit. fold zs in Hsplit.
    unfold karr_models in Hmodel. rewrite Hright in Hmodel.
    assert (Htail : (karr_eval (map v xs ++ [(-1)%Q]) zs == 0)%Q).
    { eapply Qeq_trans; [symmetry; exact Hsplit |exact Hmodel]. }
    assert (Hzs : length zs = S (length (map v xs))).
    { unfold zs. rewrite length_skipn, Hwidth, length_map. lia. }
    pose proof (karr_eval_extra_rhs (map v xs) zs Hzs) as Hdefect.
    rewrite length_map in Hdefect.
    assert (Hvalue : (karr_eval (map v xs) zs == inject_Z (karr_nth (length xs) zs))%Q).
    { setoid_rewrite Htail in Hdefect. nra. }
    subst output. change (karr_eval_coef_Q v (sparse xs zs) ==
      inject_Z (karr_nth (length xs) zs))%Q.
    setoid_rewrite <- hull_sparse_eval_Q. exact Hvalue.
  Qed.

  (** Optional output collection can use an invariant restricted to its actual input list. *)
  Lemma present_forall_in : forall A B (f : A -> option B) (R : B -> Prop) rs,
    (forall r, In r rs -> forall c, f r = Some c -> R c) ->
    Forall R (present (map f rs)).
  Proof.
    intros A B f R rs. induction rs as [|r rs IH]; intro Hresult; [constructor |].
    cbn [present map flat_map]. destruct (f r) as [c |] eqn:Hsome.
    - constructor.
      + apply Hresult with (r := r); [now left |exact Hsome].
      + apply IH. intros s Hin d Hd. apply Hresult with (r := s); [now right |exact Hd].
    - apply IH. intros s Hin d Hd. apply Hresult with (r := s); [now right |exact Hd].
  Qed.

  (** Every left equality model extends through the lifted hull construction. *)
  Lemma affine_hull_sound_Q_left : forall a b v,
    Forall (fun r => lrel r = REq -> satQ v r) a -> Forall (satQ v) (affine_hull a b).
  Proof.
    intros a b v Hmodels.
    set (xs := variables (map normalize_row a ++ map normalize_row b)).
    pose proof (hull_basis_models_left a b v Hmodels) as Hbasis.
    pose proof (hull_basis_width a b) as Hwidth.
    pose proof (hull_basis_zero_right a b) as Hright.
    fold xs in Hbasis, Hwidth, Hright.
    unfold affine_hull. fold xs. apply present_forall_in. intros r Hin c Hrow.
    apply checked_hull_row_sound_Q with (xs := xs) (a := a) (b := b) (r := r)
      (aux := map v xs ++ [1%Q]).
    - rewrite length_app, length_map. cbn [length]. lia.
    - exact (proj1 (Forall_forall _ _) Hwidth r Hin).
    - exact (proj1 (Forall_forall _ _) Hright r Hin).
    - exact (proj1 (Forall_forall _ _) Hbasis r Hin).
    - exact Hrow.
  Qed.

  (** Every right equality model extends through the lifted hull construction. *)
  Lemma affine_hull_sound_Q_right : forall a b v,
    Forall (fun r => lrel r = REq -> satQ v r) b -> Forall (satQ v) (affine_hull a b).
  Proof.
    intros a b v Hmodels.
    set (xs := variables (map normalize_row a ++ map normalize_row b)).
    pose proof (hull_basis_models_right a b v Hmodels) as Hbasis.
    pose proof (hull_basis_width a b) as Hwidth.
    pose proof (hull_basis_zero_right a b) as Hright.
    fold xs in Hbasis, Hwidth, Hright.
    unfold affine_hull. fold xs. apply present_forall_in. intros r Hin c Hrow.
    apply checked_hull_row_sound_Q with (xs := xs) (a := a) (b := b) (r := r)
      (aux := repeat 0%Q (length xs) ++ [0%Q]).
    - rewrite length_app, repeat_length. cbn [length]. lia.
    - exact (proj1 (Forall_forall _ _) Hwidth r Hin).
    - exact (proj1 (Forall_forall _ _) Hright r Hin).
    - exact (proj1 (Forall_forall _ _) Hbasis r Hin).
    - exact Hrow.
  Qed.


  Lemma leb_refl  : forall a, leb a a = true.
  Proof.
    intros [| P]; [reflexivity |]. unfold leb.
    destruct (contradiction P); [reflexivity |].
    apply forallb_forall. intros r Hin. unfold entails. apply orb_true_iff. left.
    apply existsb_exists. exists r. split; [exact Hin | apply row_eqb_refl].
  Qed.
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof.
    intros [|P] b c Hleft Hright; [destruct c; reflexivity|].
    destruct (contradiction P) as [ms|] eqn:Hempty.
    { destruct c; unfold leb; now rewrite Hempty. }
    destruct b as [|R].
    { unfold leb in Hleft. rewrite Hempty in Hleft. discriminate. }
    pose proof (leb_eq_sound_Q P R Hleft) as Hsource.
    assert (HnonemptyR : contradiction R = None).
    { destruct (contradiction R) as [ns|] eqn:HR; [|reflexivity].
      exfalso. destruct (contradiction_none_model_Q P Hempty) as [v Hmodel].
      exact (contradiction_sound_Q R ns HR v (Hsource v Hmodel)). }
    destruct c as [|S].
    { unfold leb in Hright. rewrite HnonemptyR in Hright. discriminate. }
    unfold leb in Hleft, Hright |- *. rewrite Hempty in Hleft |- *.
    rewrite HnonemptyR in Hright.
    apply forallb_forall. intros target Hin.
    pose proof (proj1 (forallb_forall _ _) Hright target Hin) as Hentail.
    unfold entails in Hentail. apply orb_true_iff in Hentail as [Hliteral|Hcert].
    - apply existsb_exists in Hliteral as [s [Hmember Hsame]].
      apply row_eqb_sound in Hsame. subst s.
      now apply (proj1 (forallb_forall _ _) Hleft).
    - destruct (entail_cert R target) as [k|] eqn:Hsome; [|discriminate].
      apply entails_complete_Q. intros v Hmodels.
      apply entail_cert_sound_Q with (P := R) (k := k); [exact Hsome|]. now apply Hsource.
  Qed.
  Lemma bot_least : forall a, leb bot a = true.
  Proof.
    intros [| P]; reflexivity.
  Qed.
  Lemma is_bot_bot : is_bot bot = true.
  Proof.
    reflexivity.
  Qed.
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof.
    intros [| P] b Hbot; [destruct b; reflexivity |].
    unfold is_bot in Hbot. destruct (contradiction P) eqn:Hempty; [| discriminate].
    destruct b; unfold leb; now rewrite Hempty.
  Qed.
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof.
    intros [|a] [|b]; try reflexivity.
    - apply leb_refl.
    - unfold join, leb. destruct (contradiction a); [reflexivity |].
      apply forallb_forall. intros r Hin. apply entails_complete_Q. intros v Hmodels.
      exact (proj1 (Forall_forall _ _) (affine_hull_sound_Q_left a b v Hmodels) r Hin).
  Qed.
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof.
    intros [|a] [|b]; try reflexivity.
    - apply leb_refl.
    - unfold join, leb. destruct (contradiction b); [reflexivity |].
      apply forallb_forall. intros r Hin. apply entails_complete_Q. intros v Hmodels.
      exact (proj1 (Forall_forall _ _) (affine_hull_sound_Q_right a b v Hmodels) r Hin).
  Qed.
  Lemma top_greatest : forall a, leb a top = true.
  Proof.
    intros [| P]; [reflexivity |]. unfold leb, top.
    destruct (contradiction P); reflexivity.
  Qed.
  Lemma widen_ub_l : forall p a b, leb a (widen p a b) = true.
  Proof.
    intros p a b. unfold widen. destruct (leb b a); [apply leb_refl |apply join_ub_l].
  Qed.
  Lemma widen_ub_r : forall p a b, leb b (widen p a b) = true.
  Proof.
    intros p a b. unfold widen. destruct (leb b a) eqn:Hle;
      [exact Hle |apply join_ub_r].
  Qed.
  Lemma widen_stable : forall p a b, leb b a = true -> widen p a b = a.
  Proof.
    intros p a b Hle. unfold widen. now rewrite Hle.
  Qed.
  Lemma wrank_widen : forall p a b, is_bot a = false -> leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Proof. Admitted. (* STUB *)
  Lemma wrank_widen_le : forall p a b, is_bot a = false -> wrank p (widen p a b) <= wrank p a.
  Proof. Admitted. (* STUB *)
  Lemma narrow_between : forall a b, leb b a = true ->
    leb b (narrow a b) = true /\ leb (narrow a b) a = true.
  Proof.
    intros a b Hle. split; [apply leb_refl | exact Hle].
  Qed.
  Lemma ngamma_mono : forall a b v, leb a b = true -> ngamma a v -> ngamma b v.
  Proof.
    intros [| P] [| Q] v Hle Hmodels; cbn [ngamma] in *; try contradiction.
    - unfold leb in Hle. destruct (contradiction P) as [ms |] eqn:Hempty;
        [| discriminate].
      exact (contradiction_sound P ms v Hempty Hmodels).
    - unfold leb in Hle. destruct (contradiction P) as [ms |] eqn:Hempty.
      + exfalso. exact (contradiction_sound P ms v Hempty Hmodels).
      + apply Forall_forall. intros r Hin.
        apply entails_sound with (P := P); [| exact Hmodels].
        now apply (proj1 (forallb_forall _ _) Hle).
  Qed.
  Lemma ngamma_bot : forall v, ~ ngamma bot v.
  Proof.
    intros v Hfalse. exact Hfalse.
  Qed.
  Lemma ngamma_top : forall v, ngamma top v.
  Proof.
    intro v. constructor.
  Qed.
  Lemma assign_sound : forall x e s st c,
    ngamma s (fun y => N.num (st y)) -> eval_term L.eval st e = Some c ->
    ngamma (assign x e s) (fun y => N.num (upd X.eqb st x c y)).
  Proof.
    intros x e [| P] st c Hmodels Heval; [contradiction |]. unfold assign.
    destruct (F.lin_of e) as [[f wrapping] |] eqn:Hform; [destruct wrapping |].
    - change (Forall (sat (fun y => N.num (upd X.eqb st x c y))) (assign_rows x f P)).
      apply numeric_update_models.
      pose proof (F.lin_sound st e c f NoWrap Heval Hform) as Hvalue.
      cbn [wrap_into] in Hvalue. rewrite Hvalue. now apply assign_rows_sound.
    - change (Forall (sat (fun y => N.num (upd X.eqb st x c y))) (project x P)).
      apply numeric_update_models. now apply project_sound.
    - change (Forall (sat (fun y => N.num (upd X.eqb st x c y))) (project x P)).
      apply numeric_update_models. now apply project_sound.
  Qed.
  Lemma havoc_sound : forall x s st c, ngamma s (fun y => N.num (st y)) ->
    ngamma (havoc x s) (fun y => N.num (upd X.eqb st x c y)).
  Proof.
    intros x [| P] st c Hmodels; [contradiction |].
    change (Forall (sat (fun y => N.num (upd X.eqb st x c y))) (project x P)).
    pose proof (project_sound x P (fun y => N.num (st y)) (N.num c) Hmodels) as Hpost.
    apply Forall_forall. intros r Hin.
    apply sat_pointwise with (v := upd X.eqb (fun y => N.num (st y)) x (N.num c)).
    - intro y. unfold upd. destruct (X.eqb y x); reflexivity.
    - now apply (proj1 (Forall_forall _ _) Hpost).
  Qed.

  (** Each equality admitted by a guard follows directly from its unwrapped atom. *)
  Lemma atom_rows_sound : forall v a, atom_holds v a -> Forall (sat v) (atom_rows a).
  Proof.
    intros v [fl wl comparison fr wr] Hatom.
    destruct wl, wr, comparison; cbn [atom_rows al alw ar arw acmp];
      try solve [constructor].
    constructor; [| constructor]. apply normalize_row_sat.
    unfold sat. cbn [lrel lhs rhs]. rewrite eval_coef_app, eval_coef_opp.
    cbn [atom_holds al alw ar arw acmp wrap_into] in Hatom.
    unfold eval_lin in Hatom. lia.
  Qed.

  Lemma assume_sound : forall g es s st cs,
    ngamma s (fun y => N.num (st y)) -> eval_terms L.eval st es = Some cs ->
    L.holds g cs -> ngamma (assume g es s) (fun y => N.num (st y)).
  Proof.
    intros g es [| P] st cs Hmodels Heval Hguard; [contradiction |].
    change (Forall (sat (fun y => N.num (st y)))
      (flat_map atom_rows (F.atoms_of g es) ++ map normalize_row P)).
    pose proof (F.atoms_sound g es st cs Heval Hguard) as Hatoms.
    apply Forall_app. split; apply Forall_forall; intros r Hin.
    - apply in_flat_map in Hin as [a [Hin Hrow]].
      pose proof (proj1 (Forall_forall _ _) Hatoms a Hin) as Hatom.
      pose proof (atom_rows_sound _ _ Hatom) as Hrows.
      now apply (proj1 (Forall_forall _ _) Hrows).
    - apply in_map_iff in Hin as [s [Hsame Hin]]. subst r.
      apply normalize_row_sat.
      now apply (proj1 (Forall_forall _ _) Hmodels).
  Qed.
  Lemma range_sound : forall e s st c,
    ngamma s (fun y => N.num (st y)) -> eval_term L.eval st e = Some c ->
    in_bnd (fst (range e s)) (snd (range e s)) (N.num c).
  Proof.
    intros e [| P] st c Hmodels Heval; [contradiction |]. unfold range.
    destruct (F.lin_of e) as [[f wrapping] |] eqn:Hform; [destruct wrapping |];
      try solve [split; exact I].
    set (xs := variables (LCons X.t (coef f) REq 0 :: P)).
    set (r := karr_target (equality_basis xs P) 1
      (KRow (map (fun x => coefficient x (coef f)) xs) 0 (repeat 0%Z (length P)) 1)).
    set (z := (- kright r / kscale r + cst f)%Z).
    destruct (entail_cert P (LCons X.t (coef f) REq (z - cst f)%Z)) as [k |]
      eqn:Hcert; [| split; exact I].
    pose proof (C.check_entails_sound P _ k (entail_cert_checked P _ k Hcert)
      (fun y => N.num (st y)) Hmodels) as Hbound.
    pose proof (F.lin_sound st e c f NoWrap Heval Hform) as Hvalue.
    cbn [sat lrel lhs rhs] in Hbound.
    cbn [wrap_into] in Hvalue. unfold eval_lin in Hvalue.
    change (z <= N.num c <= z)%Z. lia.
  Qed.
  Lemma ngamma_reached : forall P v, ngamma (Reached P) v <-> Forall (sat v) P.
  Proof.
    intros P v. reflexivity.
  Qed.
  Lemma ngamma_unreached : forall v, ~ ngamma Unreached v.
  Proof.
    intros v Hfalse. exact Hfalse.
  Qed.
End Karr.

Module KarrT (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L)
    (F : LINEARIZE_T X L N) (C : LINCERT_T X) <: KARR_ALL X L N F C.
  Include Karr X L N F C.
  Definition wsize (_ : wparam) : nat := 0.
  Definition normal (P : list (lcons X.t)) : Prop :=
    Forall (fun r => NoDup (map fst (lhs r))) P.
  Definition normal_s (s : t) : Prop :=
    match s with Unreached => True | Reached P => normal P end.
  Definition rows_of (s : t) : list (lcons X.t) :=
    match s with Unreached => nil | Reached P => P end.
  Definition vars_of (P : list (lcons X.t)) : list X.t :=
    fold_left (fun acc x => if existsb (X.eqb x) acc then acc else x :: acc)
      (flat_map (fun r => map fst (lhs r)) P) nil.
  Definition n (s : t) : nat := length (rows_of s) + length (vars_of (rows_of s)).
  Definition ell (s : t) : nat :=
    fold_right Nat.max 0 (map C.row_bits (rows_of s)) +
    fold_right Nat.max 0 (map C.row_key_bits (rows_of s)).
  Definition ellB (dim bits : nat) : nat := dim * (bits + Nat.log2 dim + 1).
  Definition elimination_work (a b : t) : nat :=
    (n a + n b + 1)^3 * (ellB (n a + n b + 1) (ell a + ell b) + 1)^2.
  Definition wunits (_ : t) : nat := 0.
  Definition terms (s : t) : nat :=
    fold_right Nat.add 0 (map (fun r => length (lhs r)) (rows_of s)).
  Definition nell (s : t) : nat := ell s + Nat.log2 (terms s) + 1.
  Definition mu (s : t) : nat := terms s + n s + nell s.
  Definition lat (m : nat) : nat :=
    (m + 2) * ((m + 1)^3 * (ellB (m + 1) m + 1)^2 + m^2 + 1).
  Definition size (s : t) : nat := lat (2 * mu s).
  Definition k_karr : N := 1. (* STUB *)
  Definition assign_work (x : X.t) (e : term L.op X.t) (s : t) : nat :=
    terms s * (nell s + 1) + (n s + tsize e + 1)^3 *
      (ellB (n s + tsize e + 1) (nell s + X.bits x + F.bits_e e) + 1)^2 +
      N.to_nat (F.T_lin_of e).
  Definition havoc_work (x : X.t) (s : t) : nat :=
    terms s * (nell s + 1) +
      (n s + 1)^3 * (ellB (n s + 1) (nell s + X.bits x) + 1)^2.
  Definition assume_work (g : L.guard) (es : list (term L.op X.t)) (s : t) : nat :=
    terms s * (nell s + 1) + (n s + fold_right Nat.add 0%nat (map tsize es) + 1)^3 *
      (ellB (n s + fold_right Nat.add 0%nat (map tsize es) + 1)
        (nell s + F.bits_es g es) + 1)^2 + N.to_nat (F.T_atoms_of g es).
  Definition range_work (e : term L.op X.t) (s : t) : nat :=
    terms s * (nell s + 1) + (n s + tsize e + 1)^3 *
      (ellB (n s + tsize e + 1) (nell s + F.bits_e e) + 1)^2 + N.to_nat (F.T_lin_of e).
  Definition range_bits (e : term L.op X.t) (s : t) : nat := range_work e s.
  TimeFun add_term.
  TimeFun normalize_coef.
  TimeFun normalize_row.
  TimeFun coefficient.
  TimeFun variables.
  TimeFun dense.
  TimeFun sparse.
  TimeFun seed_rows.
  TimeFun equality_basis.
  TimeFun empty_certificate.
  TimeFun contradiction.
  TimeFun row_eqb.
  TimeFun target_certificate.
  TimeFun entail_cert.
  TimeFun entails.
  TimeFun leb.
  TimeFun bot.
  TimeFun is_bot.
  TimeFun hull_left.
  TimeFun hull_right.
  TimeFun checked_hull_row.
  TimeFun present.
  TimeFun affine_hull.
  TimeFun join.
  TimeFun top.
  TimeFun meet.
  TimeFun widen.
  TimeFun narrow.
  TimeFun subst.
  TimeFun mentions.
  TimeFun projected_row.
  TimeFun project.
  TimeFun havoc.
  TimeFun inverse_row.
  TimeFun assign_rows.
  TimeFun assign.
  TimeFun atom_rows.
  TimeFun assume.
  TimeFun range.
  Definition c_lat : N := 1. (* STUB *)
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof. Admitted. (* STUB *)
  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_join_le : forall a b,
    (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_is_bot_le : forall s,
    (T_is_bot s <= c_lat * N.of_nat (size s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_widen_le : forall p a b,
    (T_widen p a b <= c_lat * N.of_nat
      ((wunits a + wunits b) * wsize p + (size a + size b + wsize p + 1)))%N.
  Proof. Admitted. (* STUB *)
  Definition c_num : N := 1. (* STUB *)
  Lemma T_assign_le : forall x e s,
    (T_assign x e s <= c_num * N.of_nat (assign_work x e s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_havoc_le : forall x s,
    (T_havoc x s <= c_num * N.of_nat (havoc_work x s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_assume_le : forall g es s,
    (T_assume g es s <= c_num * N.of_nat (assume_work g es s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_narrow_le : forall a b,
    (T_narrow a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_range_le : forall e s, (T_range e s <= c_num * N.of_nat (range_work e s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma range_size : forall e s,
    (N.of_nat
      (match fst (range e s) with Fin z => Z.size_nat z | _ => 0 end +
       match snd (range e s) with Fin z => Z.size_nat z | _ => 0 end) <=
     c_num * N.of_nat (range_bits e s + 1))%N.
  Proof. Admitted. (* STUB *)
  Definition c_karr : N := 1. (* STUB *)
  Lemma T_subst_le : forall x f r,
    (T_subst x f r <= c_karr * N.of_nat
      ((X.bits x + C.lsize (LCons _ (coef f) REq (cst f)) + C.lsize r + 1)^2))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_affine_hull_le : forall a b, normal a -> normal b ->
    (T_affine_hull a b <= c_karr * N.of_nat
      (elimination_work (Reached a) (Reached b)))%N.
  Proof. Admitted. (* STUB *)
  Definition k_cert : N := 1%N. (* STUB *)
  Lemma affine_hull_size : forall a b, normal a -> normal b ->
    length (affine_hull a b) <= n (Reached a) + n (Reached b) /\
    ell (Reached (affine_hull a b)) <=
      ellB (n (Reached a) + n (Reached b) + 1) (ell (Reached a) + ell (Reached b)).
  Proof. Admitted. (* STUB *)
  Lemma entail_cert_size : forall P r k, normal P -> normal (r :: nil) ->
    entail_cert P r = Some k ->
    (N.of_nat (C.csize P (mults k) + (Z.size_nat (scale k) + 1) *
        (C.lsize r + C.cbits P (mults k) + 1)) <=
      k_cert * N.of_nat (elimination_work (Reached P) (Reached (r :: nil))))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_entail_cert_le : forall P r, normal P -> normal (r :: nil) ->
    (T_entail_cert P r <= c_karr * N.of_nat
      (elimination_work (Reached P) (Reached (r :: nil))))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_join_karr_le : forall a b, normal_s a -> normal_s b ->
    (T_join a b <= c_karr * N.of_nat (((n a + n b + 1)^3)%nat) *
    N.of_nat (((ellB (n a + n b + 1) (ell a + ell b) + 1)^2)%nat))%N.
  Proof. Admitted. (* STUB *)
  (** Assignment charges row normalization and elimination after linearization. *)
  Lemma F_assign_work : forall x e s,
    (N.of_nat (assign_work x e s) = N.of_nat (terms s * (nell s + 1) +
      (n s + tsize e + 1)^3 *
      (ellB (n s + tsize e + 1) (nell s + X.bits x + F.bits_e e) + 1)^2) + F.T_lin_of e)%N.
  Proof.
    intros x e s. unfold assign_work. rewrite Nat2N.inj_add, N2Nat.id. reflexivity.
  Qed.
  (** Havoc charges row normalization and elimination of the selected variable. *)
  Lemma F_havoc_work : forall x s,
    havoc_work x s = terms s * (nell s + 1) +
      (n s + 1)^3 * (ellB (n s + 1) (nell s + X.bits x) + 1)^2.
  Proof.
    reflexivity.
  Qed.
  (** Assumption charges row normalization and elimination with the new rows. *)
  Lemma F_assume_work : forall g es s,
    (N.of_nat (assume_work g es s) = N.of_nat (terms s * (nell s + 1) +
      (n s + fold_right Nat.add 0%nat (map tsize es) + 1)^3 *
        (ellB (n s + fold_right Nat.add 0%nat (map tsize es) + 1)
          (nell s + F.bits_es g es) + 1)^2) + F.T_atoms_of g es)%N.
  Proof.
    intros g es s. unfold assume_work. rewrite Nat2N.inj_add, N2Nat.id. reflexivity.
  Qed.
  (** Top has no repeated coefficients. *)
  Lemma normal_top : normal_s top.
  Proof. Admitted. (* STUB *)
  (** Join keeps rows free of repeated keys. *)
  Lemma normal_join : forall a b, normal_s a -> normal_s b -> normal_s (join a b).
  Proof. Admitted. (* STUB *)
  (** Widening keeps rows free of repeated keys. *)
  Lemma normal_widen : forall p a b,
    normal_s a -> normal_s b -> normal_s (widen p a b).
  Proof. Admitted. (* STUB *)
  (** Narrowing keeps rows free of repeated keys. *)
  Lemma normal_narrow : forall a b, normal_s a -> normal_s b -> normal_s (narrow a b).
  Proof. Admitted. (* STUB *)
  (** Assignment normalizes its new rows. *)
  Lemma normal_assign : forall x e s, normal_s s -> normal_s (assign x e s).
  Proof. Admitted. (* STUB *)
  (** Havoc keeps rows free of repeated keys. *)
  Lemma normal_havoc : forall x s, normal_s s -> normal_s (havoc x s).
  Proof. Admitted. (* STUB *)
  (** Assumption normalizes the rows it adds. *)
  Lemma normal_assume : forall g es s, normal_s s -> normal_s (assume g es s).
  Proof. Admitted. (* STUB *)
  (** This widening has no repeated threshold search. *)
  Lemma F_wunits : forall s, wunits s = 0.
  Proof.
    reflexivity.
  Qed.
  Definition in_span (P : list (lcons X.t)) (r : lcons X.t) : Prop :=
    In r P \/
    exists ms s sc, C.combine P ms = Some s /\ lrel s = REq /\ (0 < sc)%Z /\
      (forall v : X.t -> Z, eval_coef v (lhs s) = (sc * eval_coef v (lhs r))%Z) /\
      match lrel r with
      | REq => rhs s = (sc * rhs r)%Z
      | RLe => (rhs s <= sc * rhs r)%Z
      end.
(** An equality combination assigns zero weight to every inequality source. *)
  Lemma span_equality_weights : forall P ms,
    C.admissible P ms -> C.comb_eq P ms = true -> equality_weights P ms.
  Proof.
    intros P ms [_ Hadmissible].
    induction Hadmissible as [|p m P ms Hnonnegative Htail IH]; intro Heq.
    - constructor.
    - change ((match lrel p with REq => true | RLe => Z.eqb m 0 end &&
        C.comb_eq P ms) = true) in Heq.
      apply andb_true_iff in Heq as [Hhead Hrest]. constructor.
      + intro Hrel. rewrite Hrel in Hhead. now apply Z.eqb_eq.
      + now apply IH.
  Qed.

  (** A frozen combination witness has the coefficient form of an equality certificate. *)
  Lemma span_combination_certificate : forall P r ms s sc,
    C.combine P ms = Some s -> lrel s = REq -> (0 < sc)%Z ->
    (forall v : X.t -> Z, eval_coef v (lhs s) = (sc * eval_coef v (lhs r))%Z) ->
    (match lrel r with
     | REq => rhs s = (sc * rhs r)%Z
     | RLe => (rhs s <= sc * rhs r)%Z
     end) -> equality_certificate P r ms sc.
  Proof.
    intros P r ms s sc Hcombine Hrel Hscale Heval Hright.
    pose proof (C.combine_admissible P ms s Hcombine) as Hadmissible.
    destruct (C.combine_spec P ms Hadmissible)
      as [u [Hcombined [Hcoef [Hrhs Hkind]]]].
    rewrite Hcombine in Hcombined. injection Hcombined as Hsame. subst u.
    assert (Hweights : equality_weights P ms).
    { apply span_equality_weights; [exact Hadmissible |].
      destruct (C.comb_eq P ms); [reflexivity | congruence]. }
    unfold equality_certificate. split; [exact Hweights |]. split; [exact Hscale |].
    split.
    - intro x. rewrite <- Hcoef.
      change (coefficient x (lhs s) = (sc * coefficient x (lhs r))%Z).
      rewrite !coefficient_as_eval. apply Heval.
    - destruct (lrel r); rewrite <- Hrhs; exact Hright.
  Qed.

  (** A literal equality is represented by its original position's unit vector. *)
  Lemma span_literal_certificate : forall P r,
    In r P -> lrel r = REq -> exists ms sc, equality_certificate P r ms sc.
  Proof.
    intros P r Hin Hrel. apply In_nth_error in Hin as [i Hnth].
    exists (karr_unit (length P) i), 1%Z. unfold equality_certificate.
    split; [now apply equality_weights_unit with (p := r) |]. split; [lia |]. split.
    - intro x. change (C.comb_coef P (karr_unit (length P) i) x =
        (1 * coefficient x (lhs r))%Z).
      rewrite (comb_coef_unit P i r x Hnth). ring.
    - rewrite Hrel, (comb_rhs_unit P i r Hnth). ring.
  Qed.

  (** Every equality in the frozen span has an explicit positive-scale certificate. *)
  Lemma span_equality_certificate : forall P r,
    in_span P r -> lrel r = REq -> exists ms sc, equality_certificate P r ms sc.
  Proof.
    intros P r Hspan Hrel. destruct Hspan as [Hin|[ms [s [sc Hcertificate]]]].
    - now apply span_literal_certificate.
    - destruct Hcertificate as [Hcombine [Hkind [Hscale [Heval Hrhs]]]].
      exists ms, sc. now apply span_combination_certificate with (s := s).
  Qed.

  (** Positive common denominators lift an entire equality combination to its sources. *)
  Lemma span_lift_weights : forall A B ns,
    Forall (fun r => lrel r = REq -> exists ms sc, equality_certificate A r ms sc) B ->
    equality_weights B ns ->
    exists ms d, equality_weights A ms /\ (0 < d)%Z /\
      (forall x, C.comb_coef A ms x = (d * C.comb_coef B ns x)%Z) /\
      C.comb_rhs A ms = (d * C.comb_rhs B ns)%Z.
  Proof.
    intros A B ns Hsources Hweights. revert Hsources.
    induction Hweights as [|p m B ns Hzero Hrest IH]; intro Hsources.
    - exists (repeat 0%Z (length A)), 1%Z.
      split; [apply equality_weights_zero |]. split; [lia |]. split.
      + intro x. change (row_sum A (repeat 0%Z (length A))
          (fun r => C.coef_of x (lhs r)) = (1 * 0)%Z).
        rewrite row_sum_zero. ring.
      + change (row_sum A (repeat 0%Z (length A)) rhs = (1 * 0)%Z).
        rewrite row_sum_zero. ring.
    - inversion Hsources as [|p' B' Hhead Htail]; subst p' B'.
      destruct (IH Htail) as [ms [d [Hms [Hd [Hcoef Hrhs]]]]].
      destruct (lrel p) eqn:Hrel.
      + assert (Hcertificate : exists hs hd, equality_certificate A p hs hd).
        { apply Hhead. auto. }
        destruct Hcertificate as [hs [hd [Hhs [Hhd [Hheadcoef Hheadrhs]]]]].
        rewrite Hrel in Hheadrhs.
        assert (Hlength : length ms = length hs).
        { rewrite <- (equality_weights_length A ms Hms),
            <- (equality_weights_length A hs Hhs). reflexivity. }
        exists (karr_cross hd (-(d * m))%Z ms hs), (d * hd)%Z.
        split; [now apply equality_weights_cross |]. split; [nia |]. split.
        * intro x. change (C.comb_coef A (karr_cross hd (-(d * m))%Z ms hs) x =
            ((d * hd) * (m * C.coef_of x (lhs p) + C.comb_coef B ns x))%Z).
          rewrite comb_coef_cross by exact Hlength. rewrite Hcoef, Hheadcoef. ring.
        * change (C.comb_rhs A (karr_cross hd (-(d * m))%Z ms hs) =
            ((d * hd) * (m * rhs p + C.comb_rhs B ns))%Z).
          rewrite comb_rhs_cross by exact Hlength. rewrite Hrhs, Hheadrhs. ring.
      + assert (Hm : m = 0%Z) by (apply Hzero; auto). exists ms, d.
        split; [exact Hms |]. split; [exact Hd |]. split.
        * intro x. change (C.comb_coef A ms x =
            (d * (m * C.coef_of x (lhs p) + C.comb_coef B ns x))%Z).
          rewrite Hm, Hcoef. ring.
        * change (C.comb_rhs A ms = (d * (m * rhs p + C.comb_rhs B ns))%Z).
          rewrite Hm, Hrhs. ring.
  Qed.

  (** Composing equality certificates multiplies their positive scales. *)
  Lemma span_compose_certificate : forall A B r ns sc,
    Forall (fun p => lrel p = REq -> exists ms d, equality_certificate A p ms d) B ->
    equality_certificate B r ns sc -> exists ms scale, equality_certificate A r ms scale.
  Proof.
    intros A B r ns sc Hsources [Hweights [Hscale [Hcoef Hrhs]]].
    destruct (span_lift_weights A B ns Hsources Hweights)
      as [ms [d [Hms [Hd [Hliftcoef Hliftrhs]]]]].
    exists ms, (d * sc)%Z. unfold equality_certificate.
    split; [exact Hms |]. split; [nia |]. split.
    - intro x. rewrite Hliftcoef, Hcoef. ring.
    - rewrite Hliftrhs. destruct (lrel r); nia.
  Qed.

  (** A positive-scale equality certificate reconstructs a frozen span witness. *)
  Lemma span_of_certificate : forall P r ms sc,
    equality_certificate P r ms sc -> in_span P r.
  Proof.
    intros P r ms sc [Hweights [Hscale [Hcoef Hrhs]]].
    destruct (C.combine_spec P ms (equality_weights_admissible P ms Hweights))
      as [s [Hcombine [Hcombinedcoef [Hcombinedrhs Hkind]]]].
    right. exists ms, s, sc. split; [exact Hcombine |]. split.
    - rewrite (equality_weights_comb_eq P ms Hweights) in Hkind. exact Hkind.
    - split; [exact Hscale |]. split.
      + intro v. transitivity
          (eval_coef v (map (fun p => (fst p, (sc * snd p)%Z)) (lhs r))).
        * apply eval_coef_ext. intro x. rewrite coefficient_scale.
          change (C.coef_of x (lhs s) = (sc * C.coef_of x (lhs r))%Z).
          rewrite Hcombinedcoef. apply Hcoef.
        * apply eval_coef_scale.
      + destruct (lrel r); rewrite Hcombinedrhs; exact Hrhs.
  Qed.

  (** Frozen span membership composes without assuming the source has a model. *)
  Lemma span_trans_row : forall A B r,
    Forall (in_span A) B -> in_span B r -> in_span A r.
  Proof.
    intros A B r Hsources Hspan.
    destruct Hspan as [Hin|[ns [s [sc [Hcombine [Hkind [Hscale [Heval Hrhs]]]]]]]].
    - exact (proj1 (Forall_forall _ _) Hsources r Hin).
    - assert (Hequalities : Forall
        (fun p => lrel p = REq -> exists ms d, equality_certificate A p ms d) B).
      { apply Forall_forall. intros p Hin Hrel. apply span_equality_certificate.
        - exact (proj1 (Forall_forall _ _) Hsources p Hin).
        - exact Hrel. }
      assert (Hcertificate : equality_certificate B r ns sc).
      { now apply span_combination_certificate with (s := s). }
      destruct (span_compose_certificate A B r ns sc Hequalities Hcertificate)
        as [ms [scale Hcomposed]].
      now apply span_of_certificate with (ms := ms) (sc := scale).
  Qed.

  (* Replacement body for the frozen span_trans. *)
  Lemma span_trans_draft : forall a b c,
    Forall (in_span a) b -> Forall (in_span b) c -> Forall (in_span a) c.
  Proof.
    intros a b c Hab Hbc. apply Forall_forall. intros r Hin.
    apply span_trans_row with (B := b); [exact Hab |].
    exact (proj1 (Forall_forall _ _) Hbc r Hin).
  Qed.

  (** A tracked contradiction spans the fixed false equality with a positive scale. *)
  Lemma span_of_contradiction : forall P ms, contradiction P = Some ms ->
    in_span P (LCons X.t nil REq 1%Z).
  Proof.
    intros P ms Hempty. unfold contradiction in Hempty.
    destruct (empty_certificate_has_row P _ ms Hempty)
      as [r [Hin [Hzero [Hnonzero _]]]].
    pose proof (proj1 (Forall_forall _ _)
      (equality_basis_tracks P (variables P) (LCons X.t nil REq 0%Z)) r Hin) as Htracks.
    pose proof (proj1 (Forall_forall _ _)
      (equality_basis_scale_zero P (variables P)) r Hin) as Hscale.
    assert (Hsupport : forall s, In s (LCons X.t nil REq 0%Z :: P) ->
      forall x z, In (x, z) (lhs s) -> In x (variables P)).
    { intros s Hs x z Hterm. destruct Hs as [Hsame|Hs].
      - subst s. contradiction.
      - now apply variables_contains with (r := s) (z := z). }
    pose proof (row_tracks_zero_coeff P (variables P) (LCons X.t nil REq 0%Z) r
      Htracks Hsupport Hzero) as Hcoeff.
    destruct Htracks as [Hweights [_ Hrhs]].
    assert (Hcoeffzero : forall x, C.comb_coef P (kweight r) x = 0%Z).
    { intro x. specialize (Hcoeff x). rewrite Hscale in Hcoeff. lia. }
    assert (Hright : C.comb_rhs P (kweight r) = kright r).
    { rewrite Hscale in Hrhs. lia. }
    set (sign := if (kright r <? 0)%Z then (-1)%Z else 1%Z).
    apply span_of_certificate with
      (ms := map (fun z => (sign * z)%Z) (kweight r)) (sc := Z.abs (kright r)).
    unfold equality_certificate. split; [now apply equality_weights_scale |].
    split; [destruct (kright r); cbn in *; lia |]. split.
    - intro x. rewrite comb_coef_scale, Hcoeffzero.
      change (sign * 0 = Z.abs (kright r) * 0)%Z. ring.
    - cbn [lrel rhs]. rewrite comb_rhs_scale, Hright, Z.mul_1_r.
      apply coefficient_sign_abs.
  Qed.

  (** Equality span witnesses hold under models of the source equalities alone. *)
  Lemma in_span_eq_sound_Q : forall P r,
    in_span P r -> lrel r = REq -> forall v,
    Forall (fun s => lrel s = REq -> satQ v s) P -> satQ v r.
  Proof.
    intros P r Hspan Hrel v Hmodels.
    destruct (span_equality_certificate P r Hspan Hrel) as [ms [sc Hcert]].
    now apply equality_certificate_sound_Q with (P := P) (ms := ms) (sc := sc).
  Qed.

  (** Every frozen span witness is recognized by the raw-row inclusion test. *)
  Lemma entails_of_span : forall P r, in_span P r -> entails P r = true.
  Proof.
    intros P r [Hin | [ms [s [sc [Hcombine [Hrel [Hscale [Heval Hright]]]]]]]].
    - unfold entails. apply orb_true_iff. left. apply existsb_exists.
      exists r. split; [exact Hin |apply row_eqb_refl].
    - apply entails_complete_Q. intros v Hmodels.
      apply equality_certificate_sound_Q with (P := P) (ms := ms) (sc := sc); [|exact Hmodels].
      now apply span_combination_certificate with (s := s).
  Qed.


  (** Join emits equality rows. *)
  Lemma join_eq : forall a b P, join (Reached a) (Reached b) = Reached P ->
    Forall (fun r => lrel r = REq) P.
  Proof. Admitted. (* STUB *)

  Lemma wrank_rows : forall p P, wrank p (Reached P) = length P.
  Proof.
    intros p P. reflexivity.
  Qed.
  Lemma join_independent : forall a b P, join (Reached a) (Reached b) = Reached P ->
    forall i r, nth_error P i = Some r -> ~ in_span (firstn i P ++ skipn (S i) P) r.
  Proof. Admitted. (* STUB *)
  Lemma leb_complete_span : forall a b,
    Forall (in_span a) b -> leb (Reached a) (Reached b) = true.
  Proof.
    intros a b Hspan. unfold leb. destruct (contradiction a); [reflexivity |].
    apply forallb_forall. intros r Hin. apply entails_of_span.
    now apply (proj1 (Forall_forall _ _) Hspan).
  Qed.
  Definition false_row : lcons X.t := LCons X.t nil REq 1%Z.

  Lemma span_false_contradiction : forall P,
    in_span P false_row -> exists ms, contradiction P = Some ms.
  Proof.
    intros P Hfalse. destruct (contradiction P) as [ms |] eqn:Hempty.
    - exists ms. reflexivity.
    - exfalso. destruct (contradiction_none_model_Q P Hempty) as [v Hmodels].
      pose proof (in_span_eq_sound_Q P false_row Hfalse eq_refl v Hmodels) as Hbad.
      cbn [false_row satQ lhs rhs lrel fold_right inject_Z Qeq] in Hbad. discriminate.
  Qed.
  (** Successful inclusion gives span inclusion or an infeasible left system. *)
  Lemma leb_sound_span : forall a b, leb (Reached a) (Reached b) = true ->
    Forall (in_span a) b \/ in_span a false_row.
  Proof.
    intros a b Hle. unfold leb in Hle.
    destruct (contradiction a) as [ms |] eqn:Hempty.
    - right. now apply span_of_contradiction with (ms := ms).
    - left. apply Forall_forall. intros r Hin.
      pose proof (proj1 (forallb_forall _ _) Hle r Hin) as Hentails.
      unfold entails in Hentails. apply orb_true_iff in Hentails as [Hliteral | Hcert].
      + apply existsb_exists in Hliteral as [s [Hmember Hsame]].
        apply row_eqb_sound in Hsame. subst s. now left.
      + destruct (entail_cert a r) as [k |] eqn:Hsome; [|discriminate].
        unfold entail_cert in Hsome. rewrite Hempty in Hsome.
        destruct (target_certificate a r) as [candidate |] eqn:Htarget; [|discriminate].
        apply span_of_certificate with (ms := mults candidate) (sc := scale candidate).
        now apply target_certificate_equality.
  Qed.
  (** An infeasible equality system is below every equality system. *)
  Lemma leb_false : forall a b, in_span a false_row -> leb (Reached a) (Reached b) = true.
  Proof.
    intros a b Hfalse. destruct (span_false_contradiction a Hfalse) as [ms Hempty].
    unfold leb. now rewrite Hempty.
  Qed.
  Lemma join_span : forall a b P, join (Reached a) (Reached b) = Reached P ->
    Forall (in_span a) P /\ Forall (in_span b) P.
  Proof. Admitted. (* STUB *)
  Lemma span_trans : forall a b c, Forall (in_span a) b -> Forall (in_span b) c ->
    Forall (in_span a) c.
  Proof.
    exact span_trans_draft.
  Qed.
  Definition echelon (P : list (lcons X.t)) : Prop :=
    Forall (fun r => lrel r = REq) P /\
    (forall i r, nth_error P i = Some r -> exists x a, In (x, a) (lhs r) /\ a <> 0%Z /\
      forall j s, nth_error P j = Some s -> i <> j ->
        forall b, In (x, b) (lhs s) -> b = 0%Z).
  (* STUB-CODE *)
  Definition bareiss_entries (_ : list (lcons X.t)) : list Z := nil.
  (* STUB-CODE *)
  Definition input_minors (_ : list (lcons X.t)) : list Z := nil.
  TimeFun bareiss_entries.
  TimeFun input_minors.
  Lemma subst_sat : forall v x f r, sat v (subst x f r) <->
    sat (upd X.eqb v x (eval_lin v f)) r.
  Proof.
    intros v x f r. unfold subst. rewrite normalize_row_sat.
    unfold sat. cbn [lrel lhs rhs]. rewrite eval_coef_subst.
    destruct (lrel r); lia.
  Qed.
  Lemma leb_complete_Q : forall a b, echelon a ->
    (forall v : X.t -> Q, Forall (satQ v) a -> Forall (satQ v) b) ->
    leb (Reached a) (Reached b) = true.
  Proof.
    intros a b [Hequalities _] Hsemantic. unfold leb.
    destruct (contradiction a); [reflexivity|].
    apply forallb_forall. intros target Hin. apply entails_complete_Q.
    intros v Hmodels. assert (Hfull : Forall (satQ v) a).
    { apply Forall_forall. intros r Hmember.
      apply (proj1 (Forall_forall _ _) Hmodels r Hmember).
      now apply (proj1 (Forall_forall _ _) Hequalities). }
    exact (proj1 (Forall_forall _ _) (Hsemantic v Hfull) target Hin).
  Qed.
  Lemma bareiss_minor : forall P z, In z (bareiss_entries P) -> In z (input_minors P).
  Proof. Admitted. (* STUB *)
  Lemma widen_join : forall p a b, widen p a b = if leb b a then a else join a b.
  Proof.
    reflexivity.
  Qed.
  Lemma entail_cert_checks : forall P c k,
    entail_cert P c = Some k -> C.check_entails P c k = true.
  Proof.
    exact entail_cert_checked.
  Qed.
  (** State size charges all stored numeric data. *)
  Lemma ellB_mono : forall dim dim' bits bits', dim <= dim' -> bits <= bits' ->
    ellB dim bits <= ellB dim' bits'.
  Proof.
    intros dim dim' bits bits' Hdim Hbits. unfold ellB.
    apply Nat.mul_le_mono; [exact Hdim|].
    pose proof (Nat.log2_le_mono dim dim' Hdim). lia.
  Qed.

  Lemma lat_mono : forall m n, m <= n -> lat m <= lat n.
  Proof.
    intros m n Hle. unfold lat. apply Nat.mul_le_mono; [lia|].
    apply Nat.add_le_mono; [apply Nat.add_le_mono|lia].
    - apply Nat.mul_le_mono; [apply Nat.pow_le_mono_l; lia|].
      apply Nat.pow_le_mono_l.
      pose proof (ellB_mono (m + 1) (n + 1) m n ltac:(lia) Hle). lia.
    - now apply Nat.pow_le_mono_l.
  Qed.

  Lemma lat_size : forall a b, lat (mu a + mu b) <= size a + size b.
  Proof.
    intros a b. unfold size. destruct (Nat.le_ge_cases (mu a) (mu b)) as [Hle|Hle].
    - pose proof (lat_mono (mu a + mu b) (2 * mu b) ltac:(lia)). lia.
    - pose proof (lat_mono (mu a + mu b) (2 * mu a) ltac:(lia)). lia.
  Qed.

  Lemma T1_leb : forall a b,
    (T_leb a b <= k_karr * N.of_nat (lat (mu a + mu b)))%N.
  Proof. Admitted. (* STUB *)
  Lemma T1_join : forall a b,
    (T_join a b <= k_karr * N.of_nat (lat (mu a + mu b)))%N.
  Proof. Admitted. (* STUB *)
  Lemma T1_widen : forall p a b,
    (T_widen p a b <= k_karr * N.of_nat (lat (mu a + mu b)))%N.
  Proof. Admitted. (* STUB *)
  Lemma T1_narrow : forall a b,
    (T_narrow a b <= k_karr * N.of_nat (lat (mu a + mu b)))%N.
  Proof. Admitted. (* STUB *)
  Lemma F_size : forall s, size s = lat (2 * mu s).
  Proof.
    reflexivity.
  Qed.
  (** Range work charges the numeric query and its linearization. *)
  Lemma F_range_work : forall e s, (N.of_nat (range_work e s) =
    N.of_nat (terms s * (nell s + 1) + (n s + tsize e + 1)^3 *
      (ellB (n s + tsize e + 1) (nell s + F.bits_e e) + 1)^2) + F.T_lin_of e)%N.
  Proof.
    intros e s. unfold range_work. rewrite Nat2N.inj_add, N2Nat.id. reflexivity.
  Qed.
  Lemma F_range_bits : forall e s, range_bits e s = range_work e s.
  Proof.
    reflexivity.
  Qed.
End KarrT.
