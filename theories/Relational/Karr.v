(** * Linear equality states

    Integer elimination tracks the input multipliers used by every produced row.
    For example, eliminating x from x + y = 2 and x = 1 gives y = 1.
    Builds on: KarrSig and the binary trie code. *)
From Stdlib Require Import List ZArith QArith Bool Lia Ring Permutation.
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
  (* STUB-CODE *)
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

  Lemma leb_refl  : forall a, leb a a = true.
  Proof.
    intros [| P]; [reflexivity |]. unfold leb.
    destruct (contradiction P); [reflexivity |].
    apply forallb_forall. intros r Hin. unfold entails. apply orb_true_iff. left.
    apply existsb_exists. exists r. split; [exact Hin | apply row_eqb_refl].
  Qed.
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof. Admitted. (* STUB *)
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
  Proof. Admitted. (* STUB *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof. Admitted. (* STUB *)
  Lemma top_greatest : forall a, leb a top = true.
  Proof.
    intros [| P]; [reflexivity |]. unfold leb, top.
    destruct (contradiction P); reflexivity.
  Qed.
  Lemma widen_ub_l : forall p a b, leb a (widen p a b) = true.
  Proof. Admitted. (* STUB *)
  Lemma widen_ub_r : forall p a b, leb b (widen p a b) = true.
  Proof. Admitted. (* STUB *)
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
  Proof. Admitted. (* STUB *)
  (** Havoc charges row normalization and elimination of the selected variable. *)
  Lemma F_havoc_work : forall x s,
    havoc_work x s = terms s * (nell s + 1) +
      (n s + 1)^3 * (ellB (n s + 1) (nell s + X.bits x) + 1)^2.
  Proof. Admitted. (* STUB *)
  (** Assumption charges row normalization and elimination with the new rows. *)
  Lemma F_assume_work : forall g es s,
    (N.of_nat (assume_work g es s) = N.of_nat (terms s * (nell s + 1) +
      (n s + fold_right Nat.add 0%nat (map tsize es) + 1)^3 *
        (ellB (n s + fold_right Nat.add 0%nat (map tsize es) + 1)
          (nell s + F.bits_es g es) + 1)^2) + F.T_atoms_of g es)%N.
  Proof. Admitted. (* STUB *)
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
  Proof. Admitted. (* STUB *)
  Definition in_span (P : list (lcons X.t)) (r : lcons X.t) : Prop :=
    In r P \/
    exists ms s sc, C.combine P ms = Some s /\ lrel s = REq /\ (0 < sc)%Z /\
      (forall v : X.t -> Z, eval_coef v (lhs s) = (sc * eval_coef v (lhs r))%Z) /\
      match lrel r with
      | REq => rhs s = (sc * rhs r)%Z
      | RLe => (rhs s <= sc * rhs r)%Z
      end.
  (** Join emits equality rows. *)
  Lemma join_eq : forall a b P, join (Reached a) (Reached b) = Reached P ->
    Forall (fun r => lrel r = REq) P.
  Proof. Admitted. (* STUB *)

  Lemma wrank_rows : forall p P, wrank p (Reached P) = length P.
  Proof. Admitted. (* STUB *)
  Lemma join_independent : forall a b P, join (Reached a) (Reached b) = Reached P ->
    forall i r, nth_error P i = Some r -> ~ in_span (firstn i P ++ skipn (S i) P) r.
  Proof. Admitted. (* STUB *)
  Lemma leb_complete_span : forall a b,
    Forall (in_span a) b -> leb (Reached a) (Reached b) = true.
  Proof. Admitted. (* STUB *)
  Definition false_row : lcons X.t := LCons X.t nil REq 1%Z.
  (** Successful inclusion gives span inclusion or an infeasible left system. *)
  Lemma leb_sound_span : forall a b, leb (Reached a) (Reached b) = true ->
    Forall (in_span a) b \/ in_span a false_row.
  Proof. Admitted. (* STUB *)
  (** An infeasible equality system is below every equality system. *)
  Lemma leb_false : forall a b, in_span a false_row -> leb (Reached a) (Reached b) = true.
  Proof. Admitted. (* STUB *)
  Lemma join_span : forall a b P, join (Reached a) (Reached b) = Reached P ->
    Forall (in_span a) P /\ Forall (in_span b) P.
  Proof. Admitted. (* STUB *)
  Lemma span_trans : forall a b c, Forall (in_span a) b -> Forall (in_span b) c ->
    Forall (in_span a) c.
  Proof. Admitted. (* STUB *)
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
  Proof. Admitted. (* STUB *)
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
  Lemma lat_size : forall a b, lat (mu a + mu b) <= size a + size b.
  Proof. Admitted. (* STUB *)
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
  Proof. Admitted. (* STUB *)
  (** Range work charges the numeric query and its linearization. *)
  Lemma F_range_work : forall e s, (N.of_nat (range_work e s) =
    N.of_nat (terms s * (nell s + 1) + (n s + tsize e + 1)^3 *
      (ellB (n s + tsize e + 1) (nell s + F.bits_e e) + 1)^2) + F.T_lin_of e)%N.
  Proof. Admitted. (* STUB *)
  Lemma F_range_bits : forall e s, range_bits e s = range_work e s.
  Proof. Admitted. (* STUB *)
End KarrT.
