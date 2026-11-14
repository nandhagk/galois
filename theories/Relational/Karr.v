(** * Linear equality states

    Integer elimination tracks the input multipliers used by every produced row.
    For example, eliminating x from x + y = 2 and x = 1 gives y = 1.
    Builds on: KarrSig and the binary trie code. *)
From Stdlib Require Import List ZArith NArith QArith Qfield Bool Lia Ring ArithRing Lqa Permutation.
From Argent Require Import Time Tactics Std.
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
  TimeFun seq.
  TimeFun repeat.
  TimeFun firstn.
  TimeFun skipn.
End ListDef.

Module Nat.
  TimeFun Nat.even.
  TimeFun Nat.min.
End Nat.

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

(** A certificate vector of width at least two contains a zero. *)
Lemma karr_unit_zero : forall total index,
  2 <= total -> In 0%Z (karr_unit total index).
Proof.
  intros [|[|total]] [|index] Htotal; try lia;
    cbn [karr_unit repeat List.In].
  - now right; left.
  - now left.
Qed.

(** Every stored integer is part of the augmented elimination matrix. *)
Definition karr_row_entries (r : karr_row) : list Z :=
  kcoeff r ++ kright r :: kweight r ++ [kscale r].

TimeFun karr_row_entries.

(** A live coefficient head is the first augmented matrix coordinate. *)
Lemma karr_row_entries_head : forall r,
  kcoeff r <> [] -> karr_nth 0 (karr_row_entries r) = karr_head r.
Proof.
  intros [coeff right weight scale] Hnonempty.
  destruct coeff as [|z coeff]; [contradiction|reflexivity].
Qed.

(** Restoring a processed column prepends its certified zero. *)
Lemma karr_row_entries_restore : forall r,
  karr_row_entries (karr_restore r) = 0%Z :: karr_row_entries r.
Proof.
  intros [coeff right weight scale]. reflexivity.
Qed.

(** Crossing equal-length prefixes commutes with appending their suffixes. *)
Lemma karr_cross_app : forall a b xs ys zs ws,
  length xs = length ys ->
  karr_cross a b (xs ++ zs) (ys ++ ws) =
    karr_cross a b xs ys ++ karr_cross a b zs ws.
Proof.
  intros a b xs. induction xs as [|x xs IH]; intros [|y ys] zs ws Hlength;
    cbn [length] in Hlength; try discriminate.
  - reflexivity.
  - cbn [app karr_cross]. f_equal. apply IH. lia.
Qed.

(** Every augmented row field follows the same integer cross product. *)
Lemma karr_row_entries_cross : forall a b p r,
  length (kcoeff r) = length (kcoeff p) ->
  length (kweight r) = length (kweight p) ->
  karr_row_entries (KRow (karr_cross a b (kcoeff r) (kcoeff p))
    (a * kright r - b * kright p)%Z
    (karr_cross a b (kweight r) (kweight p))
    (a * kscale r - b * kscale p)%Z) =
  karr_cross a b (karr_row_entries r) (karr_row_entries p).
Proof.
  intros a b [pc pr pw ps] [rc rr rw rs] Hcoeff Hweight.
  unfold karr_row_entries.
  cbn [kcoeff kright kweight kscale].
  rewrite (karr_cross_app a b rc pc (rr :: rw ++ [rs]) (pr :: pw ++ [ps]))
    by exact Hcoeff.
  cbn [karr_cross].
  rewrite (karr_cross_app a b rw pw [rs] [ps]) by exact Hweight.
  reflexivity.
Qed.

(** Quotienting a row divides each augmented coordinate in the same order. *)
Lemma karr_row_entries_quotient : forall d r,
  karr_row_entries (karr_quotient d r) =
    map (fun z => (z / d)%Z) (karr_row_entries r).
Proof.
  intros d [coeff right weight scale].
  unfold karr_row_entries, karr_quotient.
  cbn [kcoeff kright kweight kscale].
  rewrite !map_app. cbn [map]. rewrite map_app. cbn [map]. reflexivity.
Qed.

(** Divisibility of every augmented coordinate selects the exact quotient branch. *)
Lemma karr_exact_from_entries : forall d r,
  d <> 0%Z ->
  (forall z, In z (karr_row_entries r) -> (z mod d = 0)%Z) ->
  karr_exact d r = true.
Proof.
  intros d r Hnonzero Hentries.
  unfold karr_exact. repeat rewrite andb_true_iff. repeat split.
  - apply negb_true_iff, Z.eqb_neq. exact Hnonzero.
  - apply forallb_forall. intros z Hin. unfold karr_divisible.
    apply Z.eqb_eq, Hentries. unfold karr_row_entries.
    apply in_or_app. now left.
  - unfold karr_divisible. apply Z.eqb_eq, Hentries.
    unfold karr_row_entries. apply in_or_app. right. now left.
  - apply forallb_forall. intros z Hin. unfold karr_divisible.
    apply Z.eqb_eq, Hentries. unfold karr_row_entries.
    apply in_or_app. right. right. apply in_or_app. now left.
  - unfold karr_divisible. apply Z.eqb_eq, Hentries.
    unfold karr_row_entries. apply in_or_app. right. right.
    apply in_or_app. right. now left.
Qed.

(** The row multiplication relation multiplies every augmented coordinate. *)
Lemma karr_row_entries_multiple : forall d q r,
  karr_multiple d q r ->
  map (fun z => (d * z)%Z) (karr_row_entries q) = karr_row_entries r.
Proof.
  intros d [qc qr qw qs] [rc rr rw rs] Hmultiple.
  unfold karr_multiple in Hmultiple.
  cbn [kcoeff kright kweight kscale] in Hmultiple.
  destruct Hmultiple as [Hcoeff [Hright [Hweight Hscale]]].
  unfold karr_row_entries. cbn [kcoeff kright kweight kscale].
  rewrite !map_app. cbn [map]. rewrite map_app. cbn [map].
  rewrite Hcoeff, Hright, Hweight, Hscale. reflexivity.
Qed.

(** An integer quotient witness makes the guarded division exact. *)
Lemma karr_multiple_exact : forall d q r,
  d <> 0%Z -> karr_multiple d q r -> karr_exact d r = true.
Proof.
  intros d q r Hnonzero Hmultiple.
  apply karr_exact_from_entries; [exact Hnonzero|].
  intros z Hin.
  rewrite <- (karr_row_entries_multiple d q r Hmultiple) in Hin.
  apply in_map_iff in Hin as [entry [Hz _]]. subst z.
  rewrite Z.mul_comm. apply Z.mod_mul. exact Hnonzero.
Qed.

(** An exact reduction applies cross multiplication and quotient to all row entries. *)
Lemma karr_row_entries_reduce_exact : forall d a b p r,
  length (kcoeff r) = length (kcoeff p) ->
  length (kweight r) = length (kweight p) ->
  karr_exact d (KRow (karr_cross a b (kcoeff r) (kcoeff p))
    (a * kright r - b * kright p)%Z
    (karr_cross a b (kweight r) (kweight p))
    (a * kscale r - b * kscale p)%Z) = true ->
  karr_row_entries (karr_reduce d a b p r) =
    map (fun z => (z / d)%Z)
      (karr_cross a b (karr_row_entries r) (karr_row_entries p)).
Proof.
  intros d a b p r Hcoeff Hweight Hexact.
  unfold karr_reduce, karr_divide.
  rewrite Hexact, karr_row_entries_quotient.
  rewrite karr_row_entries_cross by assumption.
  reflexivity.
Qed.

(** Exact coordinatewise quotients multiply back to their undivided integers. *)
Lemma karr_quotient_list_multiple : forall d zs,
  d <> 0%Z -> (forall z, In z zs -> (z mod d = 0)%Z) ->
  map (fun z => (d * z)%Z) (map (fun z => (z / d)%Z) zs) = zs.
Proof.
  intros d zs Hnonzero Hdivisible. rewrite map_map.
  transitivity (map (fun z : Z => z) zs); [|apply map_id].
  apply map_ext_in. intros z Hin.
  pose proof (Z.div_mod z d Hnonzero) as Hdivision.
  pose proof (Hdivisible z Hin) as Hremainder. nia.
Qed.

(** A checked reduction scales its quotient entries back to the full cross. *)
Lemma karr_row_entries_reduce_multiple : forall d a b p r,
  length (kcoeff r) = length (kcoeff p) ->
  length (kweight r) = length (kweight p) -> d <> 0%Z ->
  karr_exact d (KRow (karr_cross a b (kcoeff r) (kcoeff p))
    (a * kright r - b * kright p)%Z
    (karr_cross a b (kweight r) (kweight p))
    (a * kscale r - b * kscale p)%Z) = true ->
  (forall z, In z (karr_cross a b (karr_row_entries r) (karr_row_entries p)) ->
    (z mod d = 0)%Z) ->
  map (fun z => (d * z)%Z) (karr_row_entries (karr_reduce d a b p r)) =
    karr_cross a b (karr_row_entries r) (karr_row_entries p).
Proof.
  intros d a b p r Hcoeff Hweight Hnonzero Hexact Hdivisible.
  rewrite (karr_row_entries_reduce_exact d a b p r Hcoeff Hweight Hexact).
  now apply karr_quotient_list_multiple.
Qed.

(** Pivot discovery removes one selected row while retaining every other row's order. *)
Lemma karr_pivot_split : forall rows pivot rest,
  karr_pivot rows = Some (pivot, rest) ->
  exists prefix suffix,
    rows = prefix ++ pivot :: suffix /\ rest = prefix ++ suffix.
Proof.
  induction rows as [|row rows IH]; intros pivot rest Hpivot; [discriminate|].
  cbn [karr_pivot] in Hpivot.
  destruct (Z.eqb (karr_head row) 0) eqn:Hzero.
  - destruct (karr_pivot rows) as [[selected remaining]|] eqn:Htail;
      [|discriminate].
    injection Hpivot as Hp Hr. subst selected rest.
    destruct (IH pivot remaining eq_refl) as [prefix [suffix [Hrows Hrest]]].
    exists (row :: prefix), suffix. subst rows. split; [reflexivity|].
    cbn [app]. now rewrite Hrest.
  - injection Hpivot as Hp Hr. subst pivot rest.
    exists [], rows. split; reflexivity.
Qed.

(** Parallel origin labels split at the same selected live row. *)
Lemma karr_forall2_split : forall A B (R : A -> B -> Prop) xs ys prefix y suffix,
  Forall2 R xs ys -> ys = prefix ++ y :: suffix ->
  exists labels label remaining,
    xs = labels ++ label :: remaining /\
    Forall2 R labels prefix /\ R label y /\ Forall2 R remaining suffix.
Proof.
  intros A B R xs ys prefix y suffix Hrel Heq.
  revert xs ys Hrel Heq.
  induction prefix as [|head prefix IH]; intros xs ys Hrel Heq; subst ys.
  - destruct xs as [|label remaining]; [inversion Hrel|].
    inversion Hrel as [|? ? ? ? Hhead Htail]; subst.
    exists [], label, remaining. repeat split; try constructor; assumption.
  - destruct xs as [|label remaining]; [inversion Hrel|].
    inversion Hrel as [|? ? ? ? Hhead Htail]; subst.
    destruct (IH remaining (prefix ++ y :: suffix) Htail eq_refl)
      as [labels [selected [tail [Hlabels [Hprefix [Hselected Hsuffix]]]]]].
    exists (label :: labels), selected, tail.
    split.
    + cbn [app]. now rewrite Hlabels.
    + split.
      * constructor; assumption.
      * split; assumption.
Qed.

(** A selected pivot keeps its matching origin label and permutes the live labels. *)
Lemma karr_pivot_with_origins : forall A (R : A -> karr_row -> Prop) labels rows pivot rest,
  Forall2 R labels rows -> karr_pivot rows = Some (pivot, rest) ->
  exists label remaining,
    Forall2 R (label :: remaining) (pivot :: rest) /\
    Permutation labels (label :: remaining).
Proof.
  intros A R labels rows pivot rest Hrel Hpivot.
  destruct (karr_pivot_split rows pivot rest Hpivot)
    as [prefix [suffix [Hrows Hrest]]].
  destruct (karr_forall2_split A karr_row R labels rows prefix pivot suffix
    Hrel Hrows) as [before [label [after [Hlabels [Hbefore [Hlabel Hafter]]]]]].
  exists label, (before ++ after). split.
  - rewrite Hrest. constructor; [exact Hlabel|].
    now apply Forall2_app.
  - rewrite Hlabels. apply Permutation_sym, Permutation_middle.
Qed.

(** Equal-length lists can always be paired by an unrestricted relation. *)
Lemma karr_forall2_true : forall A B (xs : list A) (ys : list B),
  length xs = length ys -> Forall2 (fun _ _ => True) xs ys.
Proof.
  intros A B xs. induction xs as [|x xs IH]; intros [|y ys] Hlength;
    cbn [length] in Hlength; try discriminate; [constructor|].
  constructor; [exact I|]. apply IH. lia.
Qed.

(** Combining two aligned prefixes commutes with appending their suffixes. *)
Lemma karr_combine_app : forall A B (xs : list A) (ys : list B) xs' ys',
  length xs = length ys ->
  combine (xs ++ xs') (ys ++ ys') = combine xs ys ++ combine xs' ys'.
Proof.
  intros A B xs. induction xs as [|x xs IH]; intros [|y ys] xs' ys' Hlength;
    cbn [length] in Hlength; try discriminate; [reflexivity|].
  cbn [app combine]. f_equal. apply IH. lia.
Qed.

(** Pairing a list with itself attaches each item as its own origin. *)
Lemma karr_combine_self : forall A (xs : list A),
  combine xs xs = map (fun x => (x, x)) xs.
Proof.
  intros A xs. induction xs as [|x xs IH]; cbn [combine map];
    [reflexivity|now rewrite IH].
Qed.

(** Pivot discovery permutes each original row label with its live augmented row. *)
Lemma karr_pivot_pairs_entries : forall (labels : list (list Z))
    (rows : list karr_row) (pivot : karr_row) (rest : list karr_row),
  length labels = length rows -> karr_pivot rows = Some (pivot, rest) ->
  exists label remaining,
    Permutation (combine labels (map karr_row_entries rows))
      ((label, karr_row_entries pivot) ::
        combine remaining (map karr_row_entries rest)) /\
    Permutation labels (label :: remaining) /\
    length remaining = length rest.
Proof.
  intros labels rows pivot rest Hlength Hpivot.
  destruct (karr_pivot_split rows pivot rest Hpivot)
    as [prefix [suffix [Hrows Hrest]]].
  pose proof (karr_forall2_true _ _ labels rows Hlength) as Hpaired.
  destruct (karr_forall2_split _ _ (fun _ _ => True) labels rows
    prefix pivot suffix Hpaired Hrows)
    as [before [label [after [Hlabels [Hbefore [_ Hafter]]]]]].
  pose proof (Forall2_length Hbefore) as Hbefore_length.
  pose proof (Forall2_length Hafter) as Hafter_length.
  exists label, (before ++ after). repeat split.
  - rewrite Hlabels, Hrows, Hrest. rewrite !map_app. cbn [map combine].
    rewrite (karr_combine_app _ _ before (map karr_row_entries prefix)
      (label :: after) (karr_row_entries pivot :: map karr_row_entries suffix))
      by (rewrite length_map; exact Hbefore_length).
    cbn [combine].
    rewrite (karr_combine_app _ _ before (map karr_row_entries prefix)
      after (map karr_row_entries suffix))
      by (rewrite length_map; exact Hbefore_length).
    apply Permutation_sym, Permutation_middle.
  - rewrite Hlabels. apply Permutation_sym, Permutation_middle.
  - rewrite Hrest. rewrite !length_app. lia.
Qed.

(** The instrumented run records matrix states before and after every elimination stage. *)
Fixpoint karr_bareiss_record (cols : nat) (previous : Z) (rs : list karr_row)
    : list karr_row * list Z :=
  let here := flat_map karr_row_entries rs in
  match cols with
  | 0 => (rs, here)
  | S cols =>
    match karr_pivot rs with
    | None =>
      let '(result, history) :=
        karr_bareiss_record cols previous (map karr_tail rs) in
      let output := map karr_restore result in
      (output, here ++ history ++ flat_map karr_row_entries output)
    | Some (p, rest) =>
      let a := karr_head p in
      let reduced := map (fun r => karr_reduce previous a (karr_head r) p r) rest in
      let '(result, history) := karr_bareiss_record cols a (map karr_tail reduced) in
      let output := p :: map karr_restore result in
      (output, here ++ flat_map karr_row_entries reduced ++ history ++
        flat_map karr_row_entries output)
    end
  end.

TimeFun karr_bareiss_record.

(** Recording the execution leaves its resulting basis unchanged. *)
Lemma karr_bareiss_record_value : forall cols previous rs,
  fst (karr_bareiss_record cols previous rs) = karr_bareiss cols previous rs.
Proof.
  induction cols as [|cols IH]; intros previous rs; [reflexivity|].
  cbn [karr_bareiss_record karr_bareiss].
  destruct (karr_pivot rs) as [[p rest]|].
  - rewrite map_map.
    destruct (karr_bareiss_record cols (karr_head p)
      (map (fun r => karr_tail (karr_reduce previous (karr_head p) (karr_head r) p r))
        rest)) as [result history] eqn:Hrun.
    cbn [fst]. pose proof (IH (karr_head p)
      (map (fun r => karr_tail (karr_reduce previous (karr_head p) (karr_head r) p r))
        rest)) as Hagrees.
    rewrite Hrun in Hagrees. cbn [fst] in Hagrees. now rewrite Hagrees.
  - destruct (karr_bareiss_record cols previous (map karr_tail rs))
      as [result history] eqn:Hrun.
    cbn [fst]. pose proof (IH previous (map karr_tail rs)) as Hagrees.
    rewrite Hrun in Hagrees. cbn [fst] in Hagrees. now rewrite Hagrees.
Qed.

(** Each elimination stage retains the number of live rows. *)
Lemma karr_bareiss_length : forall cols previous rows,
  length (karr_bareiss cols previous rows) = length rows.
Proof.
  induction cols as [|cols IH]; intros previous rows; [reflexivity|].
  cbn [karr_bareiss]. destruct (karr_pivot rows) as [[pivot rest]|] eqn:Hselect.
  - cbn [length]. rewrite length_map, IH, !length_map.
    destruct (karr_pivot_split rows pivot rest Hselect)
      as [prefix [suffix [Hrows Hrest]]].
    rewrite Hrows, Hrest, !length_app. cbn [length]. lia.
  - rewrite length_map, IH, length_map. reflexivity.
Qed.

(** Initial matrix entries occur in the recorded execution. *)
Lemma karr_bareiss_record_initial : forall cols previous rs z,
  In z (flat_map karr_row_entries rs) -> In z (snd (karr_bareiss_record cols previous rs)).
Proof.
  intros [|cols] previous rs z Hin; cbn [karr_bareiss_record snd]; [exact Hin|].
  destruct (karr_pivot rs) as [[p rest]|].
  - destruct (karr_bareiss_record cols (karr_head p)
      (map karr_tail
        (map (fun r => karr_reduce previous (karr_head p) (karr_head r) p r) rest))).
    cbn [snd]. apply in_or_app. now left.
  - destruct (karr_bareiss_record cols previous (map karr_tail rs)).
    cbn [snd]. apply in_or_app. now left.
Qed.

(** Final matrix entries occur in the recorded execution. *)
Lemma karr_bareiss_record_final : forall cols previous rs z,
  In z (flat_map karr_row_entries (karr_bareiss cols previous rs)) ->
  In z (snd (karr_bareiss_record cols previous rs)).
Proof.
  intros cols previous rs z Hin. rewrite <- karr_bareiss_record_value in Hin.
  destruct cols as [|cols]; cbn [karr_bareiss_record fst snd] in *; [exact Hin|].
  destruct (karr_pivot rs) as [[p rest]|].
  - destruct (karr_bareiss_record cols (karr_head p)
      (map karr_tail
        (map (fun r => karr_reduce previous (karr_head p) (karr_head r) p r) rest)));
      cbn [fst snd] in *.
    apply in_or_app. right. apply in_or_app. right. apply in_or_app. now right.
  - destruct (karr_bareiss_record cols previous (map karr_tail rs)); cbn [fst snd] in *.
    apply in_or_app. right. apply in_or_app. now right.
Qed.

(** An empty elimination input produces neither rows nor recorded entries. *)
Lemma karr_bareiss_record_empty : forall cols previous,
  karr_bareiss_record cols previous [] = ([], []).
Proof.
  induction cols as [|cols IH]; intro previous; [reflexivity|].
  cbn [karr_bareiss_record karr_pivot flat_map map].
  now rewrite IH.
Qed.

(** Every returned row entry already appears in that call's trace. *)
Lemma karr_bareiss_record_output : forall cols previous rows result history z,
  karr_bareiss_record cols previous rows = (result, history) ->
  In z (flat_map karr_row_entries result) -> In z history.
Proof.
  intros cols previous rows result history z Hrun Hin.
  pose proof (karr_bareiss_record_value cols previous rows) as Hvalue.
  rewrite Hrun in Hvalue. cbn [fst] in Hvalue.
  rewrite Hvalue in Hin.
  pose proof (karr_bareiss_record_final cols previous rows z Hin) as Htrace.
  now rewrite Hrun in Htrace.
Qed.

(** A nonempty result requires a nonempty input list. *)
Lemma karr_bareiss_record_nonempty_input : forall cols previous rows result history,
  karr_bareiss_record cols previous rows = (result, history) ->
  result <> [] -> rows <> [].
Proof.
  intros cols previous rows result history Hrun Hnonempty Hempty.
  subst rows. rewrite karr_bareiss_record_empty in Hrun.
  inversion Hrun; subst. now apply Hnonempty.
Qed.

(** Removing one column gives the smaller matrix used by Laplace expansion. *)
Fixpoint karr_delete (index : nat) (row : list Z) : list Z :=
  match index, row with
  | _, [] => []
  | 0, _ :: row => row
  | S index, z :: row => z :: karr_delete index row
  end.

TimeFun karr_delete.

(** Removing a live coefficient head deletes the first augmented coordinate. *)
Lemma karr_row_entries_tail : forall r,
  kcoeff r <> [] ->
  karr_row_entries (karr_tail r) = karr_delete 0 (karr_row_entries r).
Proof.
  intros [coeff right weight scale] Hnonempty.
  destruct coeff as [|z coeff]; [contradiction|reflexivity].
Qed.

(** A live row with zero head records zero followed by its tail entries. *)
Lemma karr_row_entries_zero_tail : forall r,
  kcoeff r <> [] -> karr_head r = 0%Z ->
  karr_row_entries r = 0%Z :: karr_row_entries (karr_tail r).
Proof.
  intros [coeff right weight scale] Hnonempty Hzero.
  destruct coeff as [|z coeff]; [contradiction|].
  cbn [karr_head kcoeff] in Hzero. subst z. reflexivity.
Qed.

(** Deleting the same coordinate preserves equality of vector widths. *)
Lemma karr_delete_length_equal : forall index xs ys,
  length xs = length ys -> length (karr_delete index xs) = length (karr_delete index ys).
Proof.
  induction index as [|index IH]; intros [|x xs] [|y ys] Hlength;
    cbn [length karr_delete] in *; try discriminate; try lia.
  f_equal. apply IH. lia.
Qed.

(** Column deletion commutes with crossing equally wide rows. *)
Lemma karr_delete_cross : forall index a b xs ys,
  length xs = length ys ->
  karr_delete index (karr_cross a b xs ys) =
    karr_cross a b (karr_delete index xs) (karr_delete index ys).
Proof.
  induction index as [|index IH]; intros a b [|x xs] [|y ys] Hlength;
    cbn [length karr_delete karr_cross] in *; try discriminate; try reflexivity.
  f_equal. apply IH. lia.
Qed.

(** Deleting two distinct columns gives the same row in either order. *)
Lemma karr_delete_comm : forall first second row,
  first <= second ->
  karr_delete first (karr_delete (S second) row) =
    karr_delete second (karr_delete first row).
Proof.
  induction first as [|first IH]; intros [|second] [|z row] Horder;
    cbn [karr_delete] in *; try reflexivity; try lia.
  f_equal. apply IH. lia.
Qed.

(** Lookup after a deletion skips precisely the removed coordinate. *)
Lemma karr_nth_delete : forall removed index row,
  karr_nth index (karr_delete removed row) =
    if index <? removed then karr_nth index row else karr_nth (S index) row.
Proof.
  intros removed index row. revert index row.
  induction removed as [|removed IH]; intros index [|z row].
  - destruct index as [|index]; cbn [karr_nth karr_delete Nat.ltb];
      try reflexivity; destruct (index <? 0); reflexivity.
  - destruct index as [|index]; reflexivity.
  - destruct index as [|index]; cbn [karr_nth karr_delete Nat.ltb];
      try reflexivity; destruct (S index <? S removed); reflexivity.
  - destruct index as [|index].
    + reflexivity.
    + cbn [karr_nth karr_delete].
      change (karr_nth index (karr_delete removed row) =
        if index <? removed then karr_nth index row else karr_nth (S index) row).
      exact (IH index row).
Qed.

(** Laplace expansion defines determinants independently of the elimination program. *)
Fixpoint karr_determinant (order : nat) (rows : list (list Z)) : Z :=
  match order with
  | 0 => 1%Z
  | S order =>
    match rows with
    | [] => 0%Z
    | row :: rows =>
      fold_right Z.add 0%Z (map (fun index =>
        ((if Nat.even index then 1 else -1) * karr_nth index row *
          karr_determinant order (map (karr_delete index) rows))%Z)
        (seq 0 (S order)))
    end
  end.

TimeFun karr_determinant.

(** One Laplace step exposes its cofactors without expanding their determinants. *)
Lemma karr_determinant_cons : forall order row rows,
  karr_determinant (S order) (row :: rows) =
    fold_right Z.add 0%Z (map (fun index =>
      ((if Nat.even index then 1 else -1) * karr_nth index row *
        karr_determinant order (map (karr_delete index) rows))%Z)
      (seq 0 (S order))).
Proof.
  reflexivity.
Qed.

(** A dense cross product has the expected value at every coordinate. *)
Lemma karr_nth_cross : forall index a b xs ys,
  length xs = length ys ->
  karr_nth index (karr_cross a b xs ys) =
    (a * karr_nth index xs - b * karr_nth index ys)%Z.
Proof.
  induction index as [|index IH]; intros a b [|x xs] [|y ys] Hlength;
    cbn [length karr_nth karr_cross] in *; try discriminate; try ring.
  apply IH. now injection Hlength.
Qed.

(** A determinant is linear in a crossed first row. *)
Lemma karr_determinant_cross : forall order a b xs ys rows,
  length xs = length ys ->
  karr_determinant (S order) (karr_cross a b xs ys :: rows) =
    (a * karr_determinant (S order) (xs :: rows) -
      b * karr_determinant (S order) (ys :: rows))%Z.
Proof.
  intros order a b xs ys rows Hlength. cbn [karr_determinant].
  generalize (seq 0 (S order)) as indices. intro indices.
  induction indices as [|index indices IH]; cbn [map fold_right]; [ring|].
  rewrite karr_nth_cross by exact Hlength. rewrite IH. ring.
Qed.

(** Crossing any selected row distributes through the whole determinant. *)
Lemma karr_determinant_cross_at : forall order prefix a b xs ys suffix,
  length prefix <= order -> length xs = length ys ->
  karr_determinant (S order) (prefix ++ karr_cross a b xs ys :: suffix) =
    (a * karr_determinant (S order) (prefix ++ xs :: suffix) -
      b * karr_determinant (S order) (prefix ++ ys :: suffix))%Z.
Proof.
  induction order as [|order IH]; intros prefix a b xs ys suffix Hprefix Hlength.
  - destruct prefix as [|row prefix]; [apply karr_determinant_cross; exact Hlength|].
    cbn [length] in Hprefix. lia.
  - destruct prefix as [|row prefix]; [apply karr_determinant_cross; exact Hlength|].
    cbn [app].
    rewrite (karr_determinant_cons (S order) row
      (prefix ++ karr_cross a b xs ys :: suffix)).
    rewrite (karr_determinant_cons (S order) row (prefix ++ xs :: suffix)).
    rewrite (karr_determinant_cons (S order) row (prefix ++ ys :: suffix)).
    generalize (seq 0 (S (S order))) as indices. intro indices.
    induction indices as [|index indices IHindices]; cbn [map fold_right]; [ring|].
    rewrite !map_app. cbn [map].
    rewrite karr_delete_cross by exact Hlength.
    pose proof (IH (map (karr_delete index) prefix) a b
      (karr_delete index xs) (karr_delete index ys)
      (map (karr_delete index) suffix)
      ltac:(rewrite length_map; cbn [length] in Hprefix; lia)
      (karr_delete_length_equal index xs ys Hlength)) as Hstep.
    rewrite Hstep, IHindices. ring.
Qed.

(** Deleting a later column leaves the first entry in place. *)
Lemma karr_delete_first : forall index row,
  karr_nth 0 (karr_delete (S index) row) = karr_nth 0 row.
Proof.
  intros index [|z row]; reflexivity.
Qed.

(** A square matrix with a zero first column has zero determinant. *)
Lemma karr_determinant_zero_first : forall order rows,
  Forall (fun row => karr_nth 0 row = 0%Z) rows ->
  karr_determinant (S order) rows = 0%Z.
Proof.
  induction order as [|order IH]; intros [|row rows] Hzero; try reflexivity.
  - inversion Hzero as [|? ? Hhead _]; subst.
    rewrite karr_determinant_cons.
    cbn [seq map fold_right karr_determinant Nat.even].
    rewrite Hhead. ring.
  - inversion Hzero as [|? ? Hhead Htail]; subst.
    rewrite karr_determinant_cons.
    generalize (seq 0 (S (S order))) as indices. intro indices.
    induction indices as [|index indices IHindices]; cbn [map fold_right]; [ring|].
    rewrite IHindices.
    destruct index as [|index].
    + rewrite Hhead. ring.
    + assert (Hminor : Forall (fun r => karr_nth 0 r = 0%Z)
          (map (karr_delete (S index)) rows)).
      { apply Forall_forall. intros r Hr.
        apply in_map_iff in Hr as [source [Hr Hsource]]. subst r.
        rewrite karr_delete_first.
        exact (proj1 (Forall_forall _ _) Htail source Hsource). }
      rewrite (IH _ Hminor). ring.
Qed.

(** Cofactors beyond the first column vanish when the remaining rows start with zero. *)
Lemma karr_laplace_tail_zero : forall order row rows indices,
  Forall (fun index => 0 < index) indices ->
  Forall (fun r => karr_nth 0 r = 0%Z) rows ->
  fold_right Z.add 0%Z (map (fun index =>
    ((if Nat.even index then 1 else -1) * karr_nth index row *
      karr_determinant (S order) (map (karr_delete index) rows))%Z) indices) = 0%Z.
Proof.
  intros order row rows indices Hpositive Hzero.
  revert Hpositive. induction indices as [|index indices IH];
    intros Hpositive; [reflexivity|].
  inversion Hpositive as [|? ? Hindex Hrest]; subst.
  cbn [map fold_right]. rewrite (IH Hrest).
  destruct index as [|index]; [lia|].
  assert (Hminor : Forall (fun r => karr_nth 0 r = 0%Z)
      (map (karr_delete (S index)) rows)).
  { apply Forall_forall. intros r Hr.
    apply in_map_iff in Hr as [source [Hr Hsource]]. subst r.
    rewrite karr_delete_first.
    exact (proj1 (Forall_forall _ _) Hzero source Hsource). }
  rewrite (karr_determinant_zero_first order _ Hminor). ring.
Qed.

(** Expansion of a matrix with zeros below its first entry is triangular. *)
Lemma karr_determinant_triangular : forall order row rows,
  Forall (fun r => karr_nth 0 r = 0%Z) rows ->
  karr_determinant (S order) (row :: rows) =
    (karr_nth 0 row * karr_determinant order (map (karr_delete 0) rows))%Z.
Proof.
  intros [|order] row rows Hzero.
  - rewrite karr_determinant_cons.
    cbn [seq map fold_right karr_determinant Nat.even]. ring.
  - rewrite karr_determinant_cons.
    change ((1 * karr_nth 0 row *
      karr_determinant (S order) (map (karr_delete 0) rows) +
      fold_right Z.add 0%Z (map (fun index =>
        ((if Nat.even index then 1 else -1) * karr_nth index row *
          karr_determinant (S order) (map (karr_delete index) rows))%Z)
        (seq 1 (S order))))%Z =
      (karr_nth 0 row *
        karr_determinant (S order) (map (karr_delete 0) rows))%Z).
    assert (Hpositive : Forall (fun index => 0 < index) (seq 1 (S order))).
    { apply Forall_forall. intros index Hin. apply in_seq in Hin. lia. }
    rewrite (karr_laplace_tail_zero order row rows _ Hpositive Hzero).
    ring.
Qed.

(** A finite sum distributes over pointwise integer addition. *)
Lemma karr_determinant_sum_add : forall A (f g : A -> Z) xs,
  fold_right Z.add 0%Z (map (fun x => (f x + g x)%Z) xs) =
    (fold_right Z.add 0%Z (map f xs) +
      fold_right Z.add 0%Z (map g xs))%Z.
Proof.
  intros A f g xs. induction xs as [|x xs IH]; cbn [map fold_right]; [ring|].
  rewrite IH. ring.
Qed.

(** The order of two finite integer summations can be exchanged. *)
Lemma karr_determinant_sum_swap : forall A B (f : A -> B -> Z) xs ys,
  fold_right Z.add 0%Z (map (fun x =>
    fold_right Z.add 0%Z (map (f x) ys)) xs) =
  fold_right Z.add 0%Z (map (fun y =>
    fold_right Z.add 0%Z (map (fun x => f x y) xs)) ys).
Proof.
  intros A B f xs. induction xs as [|x xs IH]; intro ys.
  - induction ys as [|y ys IHys]; cbn [map fold_right]; [reflexivity|].
    cbn [map fold_right] in IHys. rewrite <- IHys. ring.
  - cbn [map fold_right]. rewrite IH.
    rewrite (karr_determinant_sum_add B (f x)
      (fun y => fold_right Z.add 0%Z (map (fun a => f a y) xs)) ys).
    ring.
Qed.

(** Pointwise equality on a finite list gives equality of its integer sums. *)
Lemma karr_determinant_sum_ext : forall A (f g : A -> Z) xs,
  (forall x, In x xs -> f x = g x) ->
  fold_right Z.add 0%Z (map f xs) = fold_right Z.add 0%Z (map g xs).
Proof.
  intros A f g xs Hequal. revert Hequal.
  induction xs as [|x xs IH]; intro Hequal; [reflexivity|].
  cbn [map fold_right]. rewrite (Hequal x (or_introl eq_refl)).
  rewrite IH; [reflexivity|].
  intros y Hy. apply Hequal. now right.
Qed.

(** Negating each summand negates the finite sum. *)
Lemma karr_determinant_sum_neg : forall A (f : A -> Z) xs,
  fold_right Z.add 0%Z (map (fun x => (- f x)%Z) xs) =
    (- fold_right Z.add 0%Z (map f xs))%Z.
Proof.
  intros A f xs. induction xs as [|x xs IH]; cbn [map fold_right]; [ring|].
  rewrite IH. ring.
Qed.

(** An antisymmetric term cancels across every ordered pair of a finite list. *)
Lemma karr_determinant_pair_cancel : forall A (f : A -> A -> Z) xs,
  (forall x y, In x xs -> In y xs -> f x y = (- f y x)%Z) ->
  fold_right Z.add 0%Z (map (fun x =>
    fold_right Z.add 0%Z (map (f x) xs)) xs) = 0%Z.
Proof.
  intros A f xs Hanti.
  set (total := fold_right Z.add 0%Z (map (fun x =>
    fold_right Z.add 0%Z (map (f x) xs)) xs)).
  assert (Hneg : total = (- total)%Z).
  { unfold total.
    rewrite karr_determinant_sum_swap at 1.
    rewrite <- (karr_determinant_sum_neg A (fun y =>
      fold_right Z.add 0%Z (map (f y) xs)) xs).
    apply karr_determinant_sum_ext. intros y Hy.
    rewrite (karr_determinant_sum_ext A (fun x => f x y)
      (fun x => (- f y x)%Z) xs).
    - rewrite karr_determinant_sum_neg. reflexivity.
    - intros x Hx. apply Hanti; assumption. }
  lia.
Qed.

(** Deleted-column indices enumerate all original columns except the removed one. *)
Lemma karr_seq_delete : forall count removed,
  removed < S count ->
  map (fun index => if index <? removed then index else S index) (seq 0 count) =
    seq 0 removed ++ seq (S removed) (count - removed).
Proof.
  intros count removed Hremoved.
  replace count with (removed + (count - removed)) at 1 by lia.
  rewrite seq_app, map_app.
  f_equal.
  - transitivity (map (fun index => index) (seq 0 removed)).
    + apply map_ext_in. intros index Hin.
      apply in_seq in Hin.
      assert (Hlt : (index <? removed) = true) by (apply Nat.ltb_lt; lia).
      rewrite Hlt. reflexivity.
    + now rewrite map_id.
  - transitivity (map S (seq removed (count - removed))).
    + apply map_ext_in. intros index Hin.
      apply in_seq in Hin.
      assert (Hge : (index <? removed) = false) by (apply Nat.ltb_ge; lia).
      rewrite Hge. reflexivity.
    + now rewrite seq_shift.
Qed.

(** Concatenating finite lists adds their integer sums. *)
Lemma karr_determinant_sum_app : forall A (f : A -> Z) xs ys,
  fold_right Z.add 0%Z (map f (xs ++ ys)) =
    (fold_right Z.add 0%Z (map f xs) +
      fold_right Z.add 0%Z (map f ys))%Z.
Proof.
  intros A f xs. induction xs as [|x xs IH]; intro ys;
    cbn [app map fold_right]; [ring|].
  rewrite IH. ring.
Qed.

(** Summing through a deletion skips the removed original column. *)
Lemma karr_determinant_sum_skip : forall count removed (f : nat -> Z),
  removed < S count ->
  fold_right Z.add 0%Z (map (fun index =>
    f (if index <? removed then index else S index)) (seq 0 count)) =
  fold_right Z.add 0%Z (map (fun index =>
    if index =? removed then 0%Z else f index) (seq 0 (S count))).
Proof.
  intros count removed f Hremoved.
  set (skip := fun index => if index <? removed then index else S index).
  set (g := fun index => if index =? removed then 0%Z else f index).
  change (fold_right Z.add 0%Z (map (fun index => f (skip index)) (seq 0 count)) =
    fold_right Z.add 0%Z (map g (seq 0 (S count)))).
  rewrite <- map_map.
  unfold skip. rewrite karr_seq_delete by exact Hremoved.
  replace (S count) with (removed + S (count - removed)) by lia.
  rewrite seq_app. cbn [Nat.add].
  rewrite !karr_determinant_sum_app.
  assert (Hprefix : map g (seq 0 removed) = map f (seq 0 removed)).
  { apply map_ext_in. intros index Hin. apply in_seq in Hin.
    unfold g. assert (Hneq : (index =? removed) = false).
    { apply Nat.eqb_neq. lia. }
    now rewrite Hneq. }
  assert (Htail : fold_right Z.add 0%Z
      (map g (seq removed (S (count - removed)))) =
      fold_right Z.add 0%Z
        (map f (seq (S removed) (count - removed)))).
  { cbn [seq map fold_right].
    change ((g removed + fold_right Z.add 0%Z
      (map g (seq (S removed) (count - removed))))%Z =
      fold_right Z.add 0%Z
        (map f (seq (S removed) (count - removed)))).
    unfold g at 1. rewrite Nat.eqb_refl.
    rewrite (karr_determinant_sum_ext nat g f
      (seq (S removed) (count - removed))).
    - ring.
    - intros index Hin. apply in_seq in Hin.
      unfold g. assert (Hneq : (index =? removed) = false).
      { apply Nat.eqb_neq. lia. }
      now rewrite Hneq. }
  rewrite Hprefix, Htail. ring.
Qed.

(** Consecutive Laplace cofactors have opposite signs. *)
Lemma karr_determinant_sign_succ : forall index,
  (if Nat.even (S index) then 1 else -1)%Z =
    (- (if Nat.even index then 1 else -1))%Z.
Proof.
  induction index as [|index IH]; [reflexivity|].
  rewrite Nat.even_succ, Nat.odd_succ, IH. ring.
Qed.

(** Deleting two different columns agrees after their positions are adjusted. *)
Lemma karr_delete_two : forall first second row,
  first < second ->
  karr_delete (second - 1) (karr_delete first row) =
    karr_delete first (karr_delete second row).
Proof.
  intros first [|second] row Horder; [lia|].
  replace (S second - 1) with second by lia.
  symmetry. apply karr_delete_comm. lia.
Qed.

(** Exchanging two distinct Laplace columns reverses their combined sign. *)
Lemma karr_determinant_sign_pair : forall first second,
  first < second ->
  ((if Nat.even first then 1 else -1) *
    (if Nat.even (second - 1) then 1 else -1))%Z =
  (- ((if Nat.even second then 1 else -1) *
    (if Nat.even first then 1 else -1)))%Z.
Proof.
  intros first [|second] Horder; [lia|].
  replace (S second - 1) with second by lia.
  rewrite karr_determinant_sign_succ. ring.
Qed.

(** The minor after two deletions has a canonical increasing column order. *)
Lemma karr_delete_pair_canonical : forall first second row,
  first <> second ->
  karr_delete (if second <? first then second else second - 1)
    (karr_delete first row) =
  karr_delete (Nat.min first second)
    (karr_delete (Nat.max first second) row).
Proof.
  intros first second row Hdistinct.
  assert (Horder : first < second \/ second < first) by lia.
  destruct Horder as [Horder|Horder].
  - rewrite Nat.min_l, Nat.max_r by lia.
    assert (Htest : (second <? first) = false) by (apply Nat.ltb_ge; lia).
    rewrite Htest. apply karr_delete_two. exact Horder.
  - rewrite Nat.min_r, Nat.max_l by lia.
    assert (Htest : (second <? first) = true) by (apply Nat.ltb_lt; lia).
    now rewrite Htest.
Qed.

(** A column retained after deletion has a different original index. *)
Lemma karr_skip_index_distinct : forall removed index,
  removed <> (if index <? removed then index else S index).
Proof.
  intros removed index.
  destruct (index <? removed) eqn:Htest.
  - apply Nat.ltb_lt in Htest. lia.
  - apply Nat.ltb_ge in Htest. lia.
Qed.

(** Converting a retained original index back gives its post-deletion index. *)
Lemma karr_skip_index_inverse : forall removed index,
  (if (if index <? removed then index else S index) <? removed then
    (if index <? removed then index else S index)
   else (if index <? removed then index else S index) - 1) = index.
Proof.
  intros removed index.
  destruct (index <? removed) eqn:Htest.
  - apply Nat.ltb_lt in Htest.
    assert (Hsame : (index <? removed) = true) by (apply Nat.ltb_lt; lia).
    rewrite Hsame. reflexivity.
  - apply Nat.ltb_ge in Htest.
    assert (Hsame : (S index <? removed) = false) by (apply Nat.ltb_ge; lia).
    rewrite Hsame. lia.
Qed.

(** A pair of original columns contributes one term to a double Laplace expansion. *)
Definition karr_determinant_pair_term (order : nat) (row : list Z)
    (rows : list (list Z)) (first second : nat) : Z :=
  if first =? second then 0%Z else
    ((if Nat.even first then 1 else -1) *
      (if Nat.even (if (second <? first)%nat then second else (second - 1)%nat)
        then 1 else -1) *
      karr_nth first row * karr_nth second row *
      karr_determinant order (map (fun r =>
        karr_delete (Nat.min first second)
          (karr_delete (Nat.max first second) r)) rows))%Z.

(** Exchanging the two selected columns negates their double-expansion term. *)
Lemma karr_determinant_pair_term_swap : forall order row rows first second,
  karr_determinant_pair_term order row rows first second =
    (- karr_determinant_pair_term order row rows second first)%Z.
Proof.
  intros order row rows first second.
  destruct (Nat.eq_dec first second) as [Hequal|Hdistinct].
  - subst second. unfold karr_determinant_pair_term.
    now rewrite Nat.eqb_refl.
  - unfold karr_determinant_pair_term.
    assert (Hfirst : (first =? second) = false) by (apply Nat.eqb_neq; exact Hdistinct).
    assert (Hsecond : (second =? first) = false) by (apply Nat.eqb_neq; lia).
    rewrite Hfirst, Hsecond.
    assert (Hminor : map (fun r =>
        karr_delete (Nat.min first second)
          (karr_delete (Nat.max first second) r)) rows =
      map (fun r => karr_delete (Nat.min second first)
        (karr_delete (Nat.max second first) r)) rows).
    { rewrite (Nat.min_comm first second), (Nat.max_comm first second).
      reflexivity. }
    rewrite Hminor.
    assert (Horder : first < second \/ second < first) by lia.
    destruct Horder as [Horder|Horder].
    + assert (Hlt : (first <? second) = true) by (apply Nat.ltb_lt; lia).
      assert (Hge : (second <? first) = false) by (apply Nat.ltb_ge; lia).
      rewrite Hlt, Hge.
      rewrite (karr_determinant_sign_pair first second Horder).
      ring.
    + assert (Hlt : (second <? first) = true) by (apply Nat.ltb_lt; lia).
      assert (Hge : (first <? second) = false) by (apply Nat.ltb_ge; lia).
      rewrite Hlt, Hge.
      rewrite (karr_determinant_sign_pair second first Horder).
      ring.
Qed.

(** A post-deletion cofactor is the term for its original pair of columns. *)
Lemma karr_determinant_pair_term_skip : forall order row rows first index,
  karr_determinant_pair_term order row rows first
    (if index <? first then index else S index) =
  ((if Nat.even first then 1 else -1) * karr_nth first row *
    (if Nat.even index then 1 else -1) *
    karr_nth index (karr_delete first row) *
    karr_determinant order
      (map (karr_delete index) (map (karr_delete first) rows)))%Z.
Proof.
  intros order row rows first index.
  set (second := if index <? first then index else S index).
  assert (Hdistinct : first <> second).
  { unfold second. apply karr_skip_index_distinct. }
  assert (Hinverse :
      (if second <? first then second else second - 1) = index).
  { unfold second. apply karr_skip_index_inverse. }
  assert (Hrows : map (fun r =>
        karr_delete (Nat.min first second)
          (karr_delete (Nat.max first second) r)) rows =
      map (karr_delete index) (map (karr_delete first) rows)).
  { rewrite map_map. apply map_ext. intro r. symmetry.
    rewrite <- Hinverse. apply karr_delete_pair_canonical. exact Hdistinct. }
  unfold karr_determinant_pair_term.
  assert (Hneq : (first =? second) = false) by (apply Nat.eqb_neq; exact Hdistinct).
  rewrite Hneq, Hinverse, Hrows, karr_nth_delete.
  replace (if index <? first then karr_nth index row else karr_nth (S index) row)
    with (karr_nth second row).
  - ring.
  - unfold second. destruct (index <? first); reflexivity.
Qed.

(** A constant multiplier passes through a finite integer sum. *)
Lemma karr_determinant_sum_scale : forall A (f : A -> Z) xs factor,
  (factor * fold_right Z.add 0%Z (map f xs))%Z =
    fold_right Z.add 0%Z (map (fun x => (factor * f x)%Z) xs).
Proof.
  intros A f xs. induction xs as [|x xs IH]; intro factor;
    cbn [map fold_right]; [ring|].
  rewrite Z.mul_add_distr_l, IH. ring.
Qed.

(** Equal first two rows make every double Laplace term cancel with its reverse. *)
Lemma karr_determinant_duplicate_first : forall order row rows,
  karr_determinant (S (S order)) (row :: row :: rows) = 0%Z.
Proof.
  intros order row rows.
  rewrite karr_determinant_cons.
  transitivity (fold_right Z.add 0%Z (map (fun first =>
    fold_right Z.add 0%Z (map
      (karr_determinant_pair_term order row rows first)
      (seq 0 (S (S order))))) (seq 0 (S (S order))))).
  - apply karr_determinant_sum_ext. intros first Hfirst.
    apply in_seq in Hfirst.
    replace (map (karr_delete first) (row :: rows))
      with (karr_delete first row :: map (karr_delete first) rows) by reflexivity.
    rewrite karr_determinant_cons.
    rewrite karr_determinant_sum_scale.
    transitivity (fold_right Z.add 0%Z (map (fun index =>
      karr_determinant_pair_term order row rows first
        (if index <? first then index else S index)) (seq 0 (S order)))).
    + apply karr_determinant_sum_ext. intros index _.
      rewrite karr_determinant_pair_term_skip. ring.
    + rewrite (karr_determinant_sum_skip (S order) first
        (karr_determinant_pair_term order row rows first)) by lia.
      apply karr_determinant_sum_ext. intros second _.
      destruct (second =? first) eqn:Hsame; [|reflexivity].
      apply Nat.eqb_eq in Hsame. subst second.
      unfold karr_determinant_pair_term. now rewrite Nat.eqb_refl.
  - apply karr_determinant_pair_cancel.
    intros first second _ _. apply karr_determinant_pair_term_swap.
Qed.

(** Exchanging the first two equally wide rows reverses a determinant's sign. *)
Lemma karr_determinant_swap_first : forall order xs ys rows,
  length xs = length ys ->
  karr_determinant (S (S order)) (xs :: ys :: rows) =
    (- karr_determinant (S (S order)) (ys :: xs :: rows))%Z.
Proof.
  intros order xs ys rows Hlength.
  pose proof (karr_determinant_duplicate_first order
    (karr_cross 1 (-1) xs ys) rows) as Hzero.
  rewrite (karr_determinant_cross (S order) 1 (-1) xs ys
    (karr_cross 1 (-1) xs ys :: rows) Hlength) in Hzero.
  replace (xs :: karr_cross 1 (-1) xs ys :: rows)
    with ([xs] ++ karr_cross 1 (-1) xs ys :: rows) in Hzero by reflexivity.
  replace (ys :: karr_cross 1 (-1) xs ys :: rows)
    with ([ys] ++ karr_cross 1 (-1) xs ys :: rows) in Hzero by reflexivity.
  rewrite (karr_determinant_cross_at (S order) [xs] 1 (-1) xs ys rows)
    in Hzero by (cbn [length]; lia).
  rewrite (karr_determinant_cross_at (S order) [ys] 1 (-1) xs ys rows)
    in Hzero by (cbn [length]; lia).
  cbn [app] in Hzero.
  rewrite !karr_determinant_duplicate_first in Hzero.
  ring_simplify in Hzero. lia.
Qed.

(** Exchanging adjacent equally wide rows anywhere reverses the determinant's sign. *)
Lemma karr_determinant_swap_at : forall order prefix xs ys suffix,
  length prefix <= order -> length xs = length ys ->
  karr_determinant (S (S order)) (prefix ++ xs :: ys :: suffix) =
    (- karr_determinant (S (S order)) (prefix ++ ys :: xs :: suffix))%Z.
Proof.
  induction order as [|order IH]; intros prefix xs ys suffix Hprefix Hlength.
  - destruct prefix as [|row prefix]; [apply karr_determinant_swap_first; exact Hlength|].
    cbn [length] in Hprefix. lia.
  - destruct prefix as [|row prefix]; [apply karr_determinant_swap_first; exact Hlength|].
    cbn [app].
    rewrite (karr_determinant_cons (S (S order)) row (prefix ++ xs :: ys :: suffix)).
    rewrite (karr_determinant_cons (S (S order)) row (prefix ++ ys :: xs :: suffix)).
    generalize (seq 0 (S (S (S order)))) as indices. intro indices.
    induction indices as [|index indices IHindices]; cbn [map fold_right]; [ring|].
    rewrite !map_app. cbn [map].
    pose proof (IH (map (karr_delete index) prefix)
      (karr_delete index xs) (karr_delete index ys)
      (map (karr_delete index) suffix)
      ltac:(rewrite length_map; cbn [length] in Hprefix; lia)
      (karr_delete_length_equal index xs ys Hlength)) as Hstep.
    rewrite Hstep, IHindices. ring.
Qed.

(** Repeating a row in adjacent positions makes the determinant zero. *)
Lemma karr_determinant_duplicate_at : forall order prefix row suffix,
  length prefix <= order ->
  karr_determinant (S (S order)) (prefix ++ row :: row :: suffix) = 0%Z.
Proof.
  intros order prefix row suffix Hprefix.
  pose proof (karr_determinant_swap_at order prefix row row suffix
    Hprefix eq_refl) as Hswap.
  lia.
Qed.

(** Equal rows still cancel when equally wide rows lie between them. *)
Lemma karr_determinant_duplicate_separated : forall order prefix row middle suffix,
  length prefix + length middle <= order ->
  Forall (fun r => length r = length row) middle ->
  karr_determinant (S (S order)) (prefix ++ row :: middle ++ row :: suffix) = 0%Z.
Proof.
  intros order prefix row middle suffix Hbound Hwidth.
  revert prefix Hbound Hwidth.
  induction middle as [|r middle IH]; intros prefix Hbound Hwidth.
  - cbn [app]. apply karr_determinant_duplicate_at. lia.
  - inversion Hwidth as [|? ? Hr Htail]; subst.
    replace (prefix ++ row :: (r :: middle) ++ row :: suffix)
      with (prefix ++ row :: r :: (middle ++ row :: suffix)) by reflexivity.
    rewrite (karr_determinant_swap_at order prefix row r
      (middle ++ row :: suffix)) by (cbn [length] in *; lia).
    replace (prefix ++ r :: row :: middle ++ row :: suffix)
      with ((prefix ++ [r]) ++ row :: middle ++ row :: suffix)
      by now rewrite <- app_assoc.
    rewrite (IH (prefix ++ [r])
      ltac:(rewrite length_app; cbn [length] in *; lia) Htail).
    ring.
Qed.

(** Eliminating a later row by an earlier row scales the determinant by the pivot. *)
Lemma karr_determinant_row_reduce : forall order prefix pivot middle target suffix a h,
  length prefix + length middle <= order ->
  length target = length pivot ->
  Forall (fun r => length r = length pivot) middle ->
  karr_determinant (S (S order))
    ((prefix ++ pivot :: middle) ++ karr_cross a h target pivot :: suffix) =
  (a * karr_determinant (S (S order))
    ((prefix ++ pivot :: middle) ++ target :: suffix))%Z.
Proof.
  intros order prefix pivot middle target suffix a h Hbound Hlength Hwidth.
  rewrite (karr_determinant_cross_at (S order)
    (prefix ++ pivot :: middle) a h target pivot suffix
    ltac:(rewrite length_app; cbn [length]; lia) Hlength).
  assert (Hduplicate : karr_determinant (S (S order))
      ((prefix ++ pivot :: middle) ++ pivot :: suffix) = 0%Z).
  { replace ((prefix ++ pivot :: middle) ++ pivot :: suffix)
      with (prefix ++ pivot :: middle ++ pivot :: suffix)
      by now rewrite <- app_assoc.
    apply karr_determinant_duplicate_separated; assumption. }
  rewrite Hduplicate. ring.
Qed.

(** Permuting equal-width rows changes a determinant by at most its sign. *)
Lemma karr_determinant_permutation : forall xs ys,
  Permutation xs ys ->
  forall order prefix suffix width,
    length prefix + length xs <= S order ->
    Forall (fun row => length row = width) xs ->
    exists sign : Z, (sign = 1 \/ sign = -1)%Z /\
      karr_determinant (S order) (prefix ++ xs ++ suffix) =
        (sign * karr_determinant (S order) (prefix ++ ys ++ suffix))%Z.
Proof.
  intros xs ys Hperm.
  induction Hperm as
    [|row xs ys Hperm IH|first second xs|xs ys zs Hleft IHleft Hright IHright];
    intros order prefix suffix width Hbound Hwidth.
  - exists 1%Z. split; [now left|]. ring.
  - apply Forall_cons_iff in Hwidth as [Hrow Htail].
    destruct (IH order (prefix ++ [row]) suffix width
      ltac:(rewrite length_app; cbn [length] in *; lia) Htail)
      as [sign [Hsign Heq]].
    exists sign. split; [exact Hsign|].
    replace (prefix ++ (row :: xs) ++ suffix) with
      ((prefix ++ [row]) ++ xs ++ suffix)
      by (rewrite <- app_assoc; reflexivity).
    replace (prefix ++ (row :: ys) ++ suffix) with
      ((prefix ++ [row]) ++ ys ++ suffix)
      by (rewrite <- app_assoc; reflexivity).
    exact Heq.
  - apply Forall_cons_iff in Hwidth as [Hfirst Htail].
    apply Forall_cons_iff in Htail as [Hsecond _].
    destruct order as [|order]; [cbn [length] in Hbound; lia|].
    exists (-1)%Z. split; [now right|].
    replace (prefix ++ (first :: second :: xs) ++ suffix) with
      (prefix ++ first :: second :: (xs ++ suffix)) by reflexivity.
    replace (prefix ++ (second :: first :: xs) ++ suffix) with
      (prefix ++ second :: first :: (xs ++ suffix)) by reflexivity.
    rewrite (karr_determinant_swap_at order prefix second first (xs ++ suffix))
      by (cbn [length] in Hbound; lia).
    ring.
  - destruct (IHleft order prefix suffix width Hbound Hwidth)
      as [left [Hleft_sign Hleft_eq]].
    assert (Hmiddle_width : Forall (fun row => length row = width) ys)
      by (eapply Permutation_Forall; eauto).
    destruct (IHright order prefix suffix width
      ltac:(rewrite <- (Permutation_length Hleft); exact Hbound) Hmiddle_width)
      as [right [Hright_sign Hright_eq]].
    exists (left * right)%Z. split.
    + destruct Hleft_sign as [Hleft_one|Hleft_neg];
        destruct Hright_sign as [Hright_one|Hright_neg];
        subst; [left|right|right|left]; ring.
    + rewrite Hleft_eq, Hright_eq. ring.
Qed.

(** Choosing ordered subsequences enumerates minors without reordering their rows. *)
Fixpoint karr_choose {A} (count : nat) (xs : list A) {struct xs} : list (list A) :=
  match count with
  | 0 => [[]]
  | S count =>
    match xs with
    | [] => []
    | x :: xs => map (fun ys => x :: ys) (karr_choose count xs) ++
        karr_choose (S count) xs
    end
  end.

TimeFun karr_choose.

(** Choosing no rows gives the unique empty selection. *)
Lemma karr_choose_zero : forall A (xs : list A), karr_choose 0 xs = [[]].
Proof.
  intros A [|x xs]; reflexivity.
Qed.

(** Every enumerated choice has exactly its requested order. *)
Lemma karr_choose_length : forall A (xs : list A) order selected,
  In selected (karr_choose order xs) -> length selected = order.
Proof.
  intros A xs. induction xs as [|x xs IH]; intros [|order] selected Hin.
  - cbn [karr_choose In] in Hin. destruct Hin as [Hsame|Hin]; [now subst|contradiction].
  - contradiction.
  - rewrite karr_choose_zero in Hin. destruct Hin as [Hsame|Hin]; [now subst|contradiction].
  - cbn [karr_choose] in Hin. apply in_app_or in Hin as [Hin|Hin].
    + apply in_map_iff in Hin as [tail [Hsame Htail]]. subst selected.
      cbn [length]. f_equal. now apply IH.
    + now apply IH.
Qed.

(** Choosing one row enumerates exactly the singleton rows. *)
Lemma karr_choose_one : forall A (xs : list A),
  karr_choose 1 xs = map (fun x => [x]) xs.
Proof.
  intros A xs. induction xs as [|x xs IH]; [reflexivity|].
  cbn [karr_choose map]. rewrite karr_choose_zero, IH. reflexivity.
Qed.

(** A multiset partition contains an ordered selected subsequence. *)
Lemma karr_choose_partition : forall (original selected rest : list (list Z)),
  Permutation original (selected ++ rest) ->
  exists ordered,
    In ordered (karr_choose (length selected) original) /\
    Permutation ordered selected.
Proof.
  induction original as [|row original IH]; intros selected rest Hperm.
  - destruct selected as [|head selected].
    + exists []. split; [now rewrite karr_choose_zero; left|constructor].
    + pose proof (Permutation_length Hperm) as Hlength.
      cbn [length] in Hlength. rewrite length_app in Hlength.
      cbn [length] in Hlength. lia.
  - destruct (in_dec (list_eq_dec Z.eq_dec) row selected) as [Hin|Hout].
    + apply in_split in Hin as [before [after Hselected]]. subst selected.
      assert (Htail : Permutation original ((before ++ after) ++ rest)).
      { apply Permutation_cons_inv with (a := row).
        eapply Permutation_trans; [exact Hperm|].
        replace ((before ++ row :: after) ++ rest) with
          (before ++ row :: (after ++ rest)) by (rewrite <- app_assoc; reflexivity).
        eapply Permutation_trans.
        * apply Permutation_sym, Permutation_middle.
        * replace (row :: before ++ after ++ rest) with
            (row :: ((before ++ after) ++ rest))
            by (rewrite <- app_assoc; reflexivity).
          apply Permutation_refl. }
      destruct (IH (before ++ after) rest Htail)
        as [ordered [Hordered Hselected_perm]].
      exists (row :: ordered). split.
      * replace (length (before ++ row :: after)) with
          (S (length (before ++ after)))
          by (rewrite !length_app; cbn [length]; lia).
        cbn [karr_choose]. apply in_or_app. left.
        apply in_map_iff. exists ordered. now split.
      * eapply Permutation_trans; [apply perm_skip; exact Hselected_perm|].
        apply Permutation_middle.
    + assert (Hin : In row rest).
      { assert (Htotal : In row (selected ++ rest)).
        { eapply Permutation_in; [exact Hperm|now left]. }
        apply in_app_or in Htotal as [Hselected|Hrest];
          [contradiction|exact Hrest]. }
      apply in_split in Hin as [before [after Hrest]]. subst rest.
      assert (Htail : Permutation original (selected ++ before ++ after)).
      { apply Permutation_cons_inv with (a := row).
        eapply Permutation_trans; [exact Hperm|].
        replace (selected ++ before ++ row :: after) with
          ((selected ++ before) ++ row :: after)
          by (rewrite <- app_assoc; reflexivity).
        replace (selected ++ before ++ after) with
          ((selected ++ before) ++ after)
          by (rewrite <- app_assoc; reflexivity).
        apply Permutation_sym, Permutation_middle. }
      destruct (IH selected (before ++ after) Htail)
        as [ordered [Hordered Hselected_perm]].
      exists ordered. split.
      * destruct selected as [|head selected].
        -- rewrite karr_choose_zero in Hordered |- *. exact Hordered.
        -- cbn [karr_choose]. apply in_or_app. right. exact Hordered.
      * exact Hselected_perm.
Qed.

(** Moving one remaining label into the selected prefix preserves the source partition. *)
Lemma karr_partition_select : forall A (original prefix labels : list A) item,
  Permutation original (prefix ++ labels) -> In item labels ->
  exists rest, Permutation original ((prefix ++ [item]) ++ rest).
Proof.
  intros A original prefix labels item Hpartition Hin.
  apply in_split in Hin as [before [after Hlabels]]. subst labels.
  exists (before ++ after). eapply Permutation_trans; [exact Hpartition|].
  eapply Permutation_trans.
  - apply Permutation_app_head.
    apply Permutation_sym, Permutation_middle.
  - replace (prefix ++ item :: before ++ after) with
      ((prefix ++ [item]) ++ (before ++ after))
      by (rewrite <- app_assoc; reflexivity).
    apply Permutation_refl.
Qed.

(** Strictly increasing coordinates are the ordered selections of a source range. *)
Fixpoint karr_increasing (columns : list nat) : Prop :=
  match columns with
  | [] => True
  | column :: columns =>
    Forall (fun later => column < later) columns /\ karr_increasing columns
  end.

(** Consecutive coordinates are strictly increasing. *)
Lemma karr_increasing_seq : forall start count,
  karr_increasing (seq start count).
Proof.
  intros start count. revert start. induction count as [|count IH]; intro start.
  - exact I.
  - cbn [seq karr_increasing]. split; [|apply IH].
    apply Forall_forall. intros column Hin. apply in_seq in Hin. lia.
Qed.

(** Every prefix of an increasing coordinate list is increasing. *)
Lemma karr_increasing_prefix : forall prefix suffix,
  karr_increasing (prefix ++ suffix) -> karr_increasing prefix.
Proof.
  induction prefix as [|head prefix IH]; intros suffix Hinc; [exact I|].
  cbn [app karr_increasing] in Hinc |- *.
  destruct Hinc as [Hafter Htail]. split.
  - apply Forall_app in Hafter as [Hprefix _]. exact Hprefix.
  - now apply IH with (suffix := suffix).
Qed.

(** Every coordinate of a consecutive range lies below its endpoint. *)
Lemma karr_seq_bounded : forall start count,
  Forall (fun column => column < start + count) (seq start count).
Proof.
  intros start count. apply Forall_forall. intros column Hin.
  apply in_seq in Hin. lia.
Qed.

(** Appending any later coordinate preserves the strict prefix order. *)
Lemma karr_increasing_prefix_member : forall prefix suffix column,
  karr_increasing (prefix ++ suffix) -> In column suffix ->
  karr_increasing (prefix ++ [column]).
Proof.
  induction prefix as [|head prefix IH]; intros suffix column Hinc Hin.
  - cbn [app karr_increasing]. split; [constructor|exact I].
  - cbn [app karr_increasing] in *. destruct Hinc as [Hafter Htail].
    split.
    + apply Forall_app. split.
      * apply (proj1 (Forall_app _ _ _)) in Hafter as [Hprefix _].
        exact Hprefix.
      * constructor; [|constructor].
        apply (proj1 (Forall_forall _ _) Hafter).
        apply in_or_app. now right.
    + apply IH with (suffix := suffix); assumption.
Qed.

(** Dropping the next coordinate keeps the chosen and live columns increasing. *)
Lemma karr_increasing_skip : forall prefix head suffix,
  karr_increasing (prefix ++ head :: suffix) ->
  karr_increasing (prefix ++ suffix).
Proof.
  induction prefix as [|first prefix IH]; intros head suffix Hinc.
  - cbn [app karr_increasing] in Hinc |- *. exact (proj2 Hinc).
  - cbn [app karr_increasing] in *. destruct Hinc as [Hafter Htail].
    split.
    + apply Forall_app in Hafter as [Hprefix Hrest].
      apply Forall_app. split; [exact Hprefix|].
      inversion Hrest as [|? ? _ Hsuffix]; subst. exact Hsuffix.
    + now apply IH with (head := head).
Qed.

(** Every bounded increasing coordinate list is enumerated by choose. *)
Lemma karr_choose_seq_increasing : forall count start columns,
  karr_increasing columns ->
  Forall (fun column => start <= column /\ column < start + count) columns ->
  In columns (karr_choose (length columns) (seq start count)).
Proof.
  induction count as [|count IH]; intros start [|column columns] Hinc Hrange.
  - rewrite karr_choose_zero. now left.
  - cbn [karr_increasing] in Hinc.
    inversion Hrange as [|? ? [Hlow Hhigh] _]; subst. lia.
  - rewrite karr_choose_zero. now left.
  - cbn [karr_increasing] in Hinc. destruct Hinc as [Hafter Htail].
    inversion Hrange as [|? ? [Hlow Hhigh] Hrest]; subst.
    cbn [seq karr_choose length].
    destruct (Nat.eq_dec column start) as [Heq|Hneq].
    + subst column. apply in_or_app. left.
      apply in_map_iff. exists columns. split; [reflexivity|].
      apply IH; [exact Htail|].
      apply Forall_forall. intros later Hin.
      pose proof (proj1 (Forall_forall _ _) Hafter later Hin) as Hlater.
      pose proof (proj1 (Forall_forall _ _) Hrest later Hin) as [_ Hbound].
      cbn in Hlater, Hbound. lia.
    + apply in_or_app. right.
      apply IH.
      * cbn [karr_increasing]. now split.
      * constructor.
        -- cbn [length] in *. lia.
        -- apply Forall_forall. intros later Hin.
           pose proof (proj1 (Forall_forall _ _) Hafter later Hin) as Hlater.
           pose proof (proj1 (Forall_forall _ _) Hrest later Hin) as [_ Hbound].
           cbn in Hlater, Hbound. lia.
Qed.

(** An enumerated selection cannot exceed its source list. *)
Lemma karr_choose_count_le : forall A (source : list A) count selected,
  In selected (karr_choose count source) -> count <= length source.
Proof.
  intros A source. induction source as [|x source IH]; intros [|count] selected Hin;
    cbn [karr_choose length] in *; try lia; try contradiction.
  apply in_app_or in Hin as [Hin|Hin].
  - apply in_map_iff in Hin as [tail [_ Htail]].
    pose proof (IH count tail Htail). lia.
  - pose proof (IH (S count) selected Hin). lia.
Qed.

(** A lookup before the end of a list returns one of its elements. *)
Lemma karr_nth_list_member : forall A (source : list A) default index,
  index < length source -> In (nth index source default) source.
Proof.
  intros A source. induction source as [|head source IH]; intros default [|index] Hindex;
    cbn [length nth List.In] in *; try lia.
  - now left.
  - right. apply IH. lia.
Qed.

(** A selected row and column set determines one square submatrix. *)
Definition karr_submatrix (columns : list nat) (rows : list (list Z)) : list (list Z) :=
  map (fun row => map (fun index => karr_nth index row) columns) rows.

TimeFun karr_submatrix.

(** Selecting columns fixes every output row width. *)
Lemma karr_submatrix_width : forall columns rows,
  Forall (fun row => length row = length columns) (karr_submatrix columns rows).
Proof.
  intros columns rows. unfold karr_submatrix. apply Forall_map.
  apply Forall_forall. intros row _. apply length_map.
Qed.

(** Selecting columns commutes with crossing two equally wide rows. *)
Lemma karr_select_cross : forall columns a b xs ys,
  length xs = length ys ->
  map (fun i => karr_nth i (karr_cross a b xs ys)) columns =
    karr_cross a b (map (fun i => karr_nth i xs) columns)
      (map (fun i => karr_nth i ys) columns).
Proof.
  intros columns a b xs ys Hwidth.
  induction columns as [|i columns IH]; [reflexivity|].
  cbn [map karr_cross]. rewrite karr_nth_cross by exact Hwidth.
  now rewrite IH.
Qed.

(** Crossing rows of equal width preserves their width. *)
Lemma karr_cross_length : forall a b xs ys,
  length xs = length ys -> length (karr_cross a b xs ys) = length xs.
Proof.
  intros a b xs. induction xs as [|x xs IH]; intros [|y ys] Hwidth;
    cbn [length karr_cross] in *; try discriminate; try reflexivity.
  f_equal. apply IH. lia.
Qed.

(** Crossing each row below a pivot multiplies the determinant once per row. *)
Lemma karr_determinant_cross_rows : forall p prefix xs a (f : list Z -> Z),
  Forall (fun r => length r = length p) (prefix ++ xs) ->
  karr_determinant (S (length prefix + length xs))
    (p :: prefix ++ map (fun x => karr_cross a (f x) x p) xs) =
  (a ^ Z.of_nat (length xs) *
    karr_determinant (S (length prefix + length xs)) (p :: prefix ++ xs))%Z.
Proof.
  intros p prefix xs a f Hwidth. revert prefix Hwidth.
  induction xs as [|x xs IH]; intros prefix Hwidth.
  - cbn [length map app]. rewrite Z.pow_0_r. ring.
  - apply Forall_app in Hwidth as [Hprefix Hrest].
    inversion Hrest as [|? ? Hx Htail]; subst.
    assert (Hnext : Forall (fun r => length r = length p) ((prefix ++ [x]) ++ xs)).
    { apply Forall_app. split; [apply Forall_app; split; [exact Hprefix|constructor;
        [exact Hx|constructor]]|exact Htail]. }
    specialize (IH (prefix ++ [x]) Hnext).
    replace (S (length prefix + length (x :: xs))) with
      (S (S (length prefix + length xs))) by (cbn [length]; lia).
    cbn [map].
    replace (p :: prefix ++ karr_cross a (f x) x p ::
      map (fun y => karr_cross a (f y) y p) xs) with
      (([] ++ p :: prefix) ++ karr_cross a (f x) x p ::
        map (fun y => karr_cross a (f y) y p) xs) by reflexivity.
    rewrite (karr_determinant_row_reduce (length prefix + length xs)
      [] p prefix x (map (fun y => karr_cross a (f y) y p) xs) a (f x))
      by (cbn [length app]; try lia; exact Hprefix).
    replace (S (length (prefix ++ [x]) + length xs)) with
      (S (S (length prefix + length xs))) in IH
      by (rewrite length_app; cbn [length]; lia).
    replace (([] ++ p :: prefix) ++ x ::
      map (fun y => karr_cross a (f y) y p) xs) with
      (p :: prefix ++ x :: map (fun y => karr_cross a (f y) y p) xs)
      by reflexivity.
    replace (p :: (prefix ++ [x]) ++ xs) with (p :: prefix ++ x :: xs)
      in IH by (rewrite <- app_assoc; reflexivity).
    replace (p :: prefix ++ x :: map (fun y => karr_cross a (f y) y p) xs)
      with (p :: (prefix ++ [x]) ++ map (fun y => karr_cross a (f y) y p) xs)
      by (rewrite <- app_assoc; reflexivity).
    rewrite IH. cbn [length]. rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    ring.
Qed.

(** Crossing a row against itself with zero second factor scales every entry. *)
Lemma karr_cross_scale : forall a xs,
  karr_cross a 0 xs xs = map (fun z => (a * z)%Z) xs.
Proof.
  intros a xs. induction xs as [|x xs IH]; [reflexivity|].
  cbn [karr_cross map]. rewrite IH. f_equal. ring.
Qed.

(** Scaling several selected rows scales the determinant by one factor per row. *)
Lemma karr_determinant_scale_rows : forall order prefix rows suffix a,
  length prefix + length rows <= order ->
  karr_determinant order
    (prefix ++ map (map (fun z => (a * z)%Z)) rows ++ suffix) =
  (a ^ Z.of_nat (length rows) *
    karr_determinant order (prefix ++ rows ++ suffix))%Z.
Proof.
  intros order prefix rows. revert prefix.
  induction rows as [|row rows IH]; intros prefix suffix a Hbound.
  - cbn [map length app]. rewrite Z.pow_0_r. ring.
  - destruct order as [|order]; [cbn [length] in Hbound; lia|].
    cbn [map length].
    rewrite <- karr_cross_scale.
    rewrite app_assoc.
    replace ((prefix ++ karr_cross a 0 row row ::
      map (map (fun z => (a * z)%Z)) rows) ++ suffix) with
      (prefix ++ karr_cross a 0 row row ::
        (map (map (fun z => (a * z)%Z)) rows ++ suffix))
      by (rewrite <- app_assoc; reflexivity).
    cbn [length] in Hbound.
    rewrite (karr_determinant_cross_at order prefix a 0 row row
      (map (map (fun z => (a * z)%Z)) rows ++ suffix)) by lia.
    specialize (IH (prefix ++ [row]) suffix a ltac:(rewrite length_app;
      cbn [length] in *; lia)).
    replace (prefix ++ row :: map (map (fun z => (a * z)%Z)) rows ++ suffix)
      with ((prefix ++ [row]) ++ map (map (fun z => (a * z)%Z)) rows ++ suffix)
      by (rewrite <- app_assoc; reflexivity).
    rewrite IH.
    replace ((prefix ++ [row]) ++ rows ++ suffix)
      with (prefix ++ row :: rows ++ suffix)
      by (rewrite <- app_assoc; reflexivity).
    rewrite Nat2Z.inj_succ, Z.pow_succ_r by lia.
    replace (prefix ++ (row :: rows) ++ suffix)
      with (prefix ++ row :: rows ++ suffix)
      by reflexivity.
    ring.
Qed.

(** A selected pivot column and its suffix commute with every crossed row. *)
Lemma karr_stage_cross_selected : forall c p xs ys,
  Forall (fun x => length x = length p) xs ->
  karr_submatrix (c :: ys)
    (map (fun x => karr_cross (karr_nth c p) (karr_nth c x) x p) xs) =
  map (fun row => karr_cross (karr_nth c p) (karr_nth 0 row) row
    (map (fun i => karr_nth i p) (c :: ys))) (karr_submatrix (c :: ys) xs).
Proof.
  intros c p xs ys Hwidth. unfold karr_submatrix. rewrite !map_map.
  apply map_ext_in. intros x Hin. cbn [map].
  rewrite karr_select_cross.
  - rewrite karr_nth_cross by
      exact (proj1 (Forall_forall _ _) Hwidth x Hin).
    reflexivity.
  - exact (proj1 (Forall_forall _ _) Hwidth x Hin).
Qed.

(** Removing the selected first column leaves precisely the suffix selection. *)
Lemma karr_stage_selected_tail : forall c ys xs,
  map (karr_delete 0) (karr_submatrix (c :: ys) xs) =
    karr_submatrix ys xs.
Proof.
  intros c ys xs. unfold karr_submatrix. rewrite map_map.
  apply map_ext. intro x. reflexivity.
Qed.

(** Selecting after deletion is selecting the successor coordinates before it. *)
Lemma karr_submatrix_delete_first : forall selected rows,
  karr_submatrix selected (map (karr_delete 0) rows) =
    karr_submatrix (map S selected) rows.
Proof.
  intros selected rows. unfold karr_submatrix. rewrite !map_map.
  apply map_ext. intro row. rewrite map_map.
  apply map_ext. intro index. now rewrite karr_nth_delete.
Qed.

(** One undivided elimination stage scales every selected minor. *)
Lemma karr_stage_minor : forall (c : nat) (p : list Z) (xs : list (list Z)) (ys : list nat),
  karr_nth c p <> 0%Z ->
  Forall (fun x => length x = length p) xs ->
  length ys = length xs -> 1 <= length xs ->
  karr_determinant (length ys)
    (karr_submatrix ys
      (map (fun x => karr_cross (karr_nth c p) (karr_nth c x) x p) xs)) =
  (karr_nth c p ^ Z.of_nat (length xs - 1) *
   karr_determinant (S (length ys)) (karr_submatrix (c :: ys) (p :: xs)))%Z.
Proof.
  intros c p xs ys Ha Hsource Hcolumns Hpositive.
  set (a := karr_nth c p).
  set (pivot := map (fun i => karr_nth i p) (c :: ys)).
  set (rows := karr_submatrix (c :: ys) xs).
  set (crossed := map (fun row => karr_cross a (karr_nth 0 row) row pivot) rows).
  assert (Hwidth : Forall (fun row => length row = length pivot) rows).
  { unfold rows, pivot. pose proof (karr_submatrix_width (c :: ys) xs) as Hrows.
    rewrite length_map. exact Hrows. }
  assert (Hlength : length rows = length ys).
  { unfold rows, karr_submatrix. rewrite length_map. lia. }
  assert (Hzero : Forall (fun row => karr_nth 0 row = 0%Z) crossed).
  { unfold crossed. apply Forall_forall. intros row Hin.
    apply in_map_iff in Hin as [source [Hrow Hsource_row]]. subst row.
    rewrite karr_nth_cross by
      exact (proj1 (Forall_forall _ _) Hwidth source Hsource_row).
    unfold a, pivot. cbn [map karr_nth]. ring. }
  pose proof (karr_determinant_cross_rows pivot [] rows a
    (fun row => karr_nth 0 row) Hwidth) as Hcross.
  cbn [length app] in Hcross. rewrite Hlength in Hcross.
  pose proof (karr_determinant_triangular (length ys) pivot crossed Hzero) as Htri.
  assert (Hselected : map (karr_delete 0) crossed =
    karr_submatrix ys
      (map (fun x => karr_cross (karr_nth c p) (karr_nth c x) x p) xs)).
  { unfold crossed, rows, pivot, a.
    rewrite <- (karr_stage_cross_selected c p xs ys Hsource).
    apply karr_stage_selected_tail. }
  rewrite Hselected in Htri.
  destruct (length xs) as [|m] eqn:Hm; [lia|].
  assert (Hy : length ys = S m) by lia.
  rewrite Hy in Hcross, Htri.
  assert (Hhead : karr_nth 0 pivot = a) by (unfold pivot, a; reflexivity).
  rewrite Hhead in Htri.
  cbn [Nat.add] in Hcross.
  fold crossed in Hcross.
  rewrite Htri in Hcross.
  rewrite Nat2Z.inj_succ, Z.pow_succ_r in Hcross by lia.
  unfold a, pivot, rows in Hcross.
  unfold a in Ha.
  rewrite Hy. cbn [Nat.sub]. rewrite Nat.sub_0_r. unfold a.
  change (karr_determinant (S m)
    (karr_submatrix ys
      (map (fun x => karr_cross (karr_nth c p) (karr_nth c x) x p) xs)) =
    ((karr_nth c p ^ Z.of_nat m)%Z *
      karr_determinant (S (S m))
        (map (fun i => karr_nth i p) (c :: ys) ::
          karr_submatrix (c :: ys) xs))%Z).
  nia.
Qed.

(** Every selected live minor is tied to its labeled original rows and columns. *)
Definition karr_minor_law (previous : Z) (pivot_rows : list (list Z))
    (pivot_columns columns : list nat) (pairs : list (list Z * list Z)) : Prop :=
  forall origins live selected,
    Forall2 (fun origin row => In (origin, row) pairs) origins live ->
    length selected = length live ->
    Forall (fun i => i < length columns) selected ->
    1 <= length live ->
    karr_determinant (length selected) (karr_submatrix selected live) =
      (previous ^ Z.of_nat (length live - 1) *
        karr_determinant (length pivot_rows + length live)
          (karr_submatrix
            (pivot_columns ++ map (fun i => nth i columns 0%nat) selected)
            (pivot_rows ++ origins)))%Z.

(** Reordering the live row-label pairs leaves their minor equations intact. *)
Lemma karr_minor_law_permutation : forall previous pivot_rows pivot_columns columns
    pairs reordered,
  Permutation pairs reordered ->
  karr_minor_law previous pivot_rows pivot_columns columns pairs ->
  karr_minor_law previous pivot_rows pivot_columns columns reordered.
Proof.
  intros previous pivot_rows pivot_columns columns pairs reordered Hperm Hlaw.
  unfold karr_minor_law in *. intros origins live selected Hpaired Hlength Hcolumns Hpositive.
  apply Hlaw; try assumption.
  eapply Forall2_impl; [|exact Hpaired].
  intros origin row Hin. eapply Permutation_in; [apply Permutation_sym; exact Hperm|].
  exact Hin.
Qed.

(** A valid index in the original coordinate sequence names itself. *)
Lemma karr_nth_seq : forall count start index,
  index < count -> nth index (seq start count) 0%nat = start + index.
Proof.
  induction count as [|count IH]; intros start [|index] Hindex;
    [lia|lia|cbn [seq nth]; lia|].
  - cbn [seq nth]. rewrite IH by lia. lia.
Qed.

(** The original augmented matrix satisfies the all-order law at stage zero. *)
Lemma karr_minor_law_initial : forall originals width,
  karr_minor_law 1 [] [] (seq 0 width)
    (map (fun row => (row, row)) originals).
Proof.
  intros originals width. unfold karr_minor_law.
  intros origins live selected Hpaired Hlength Hselected Hpositive.
  assert (Hsame : origins = live).
  { clear Hlength Hselected Hpositive.
    induction Hpaired as [|origin row origins live Hin Htail IH];
      [reflexivity|].
    apply in_map_iff in Hin as [source [Heq _]].
    inversion Heq; subst. now f_equal. }
  subst origins.
  assert (Hcolumns : map (fun i => nth i (seq 0 width) 0%nat) selected = selected).
  { clear Hlength Hpositive Hpaired.
    revert Hselected. induction selected as [|i selected IH]; intro Hselected;
      [reflexivity|].
    inversion Hselected as [|? ? Hi Hrest]; subst. cbn [map]. f_equal.
    - rewrite length_seq in Hi. rewrite karr_nth_seq by exact Hi. lia.
    - now apply IH. }
  rewrite Hcolumns, Z.pow_1_l.
  - cbn [length app Nat.add]. rewrite Hlength. ring.
  - lia.
Qed.

(** Every selected row after a skipped column retains its original live label. *)
Lemma karr_pairs_delete_first_lift : forall (pairs : list (list Z * list Z))
    (origins live : list (list Z)),
  Forall2 (fun origin row => In (origin, row)
    (map (fun pair => (fst pair, karr_delete 0 (snd pair))) pairs)) origins live ->
  exists prior,
    Forall2 (fun origin row => In (origin, row) pairs) origins prior /\
    live = map (karr_delete 0) prior.
Proof.
  intros pairs origins live Hpaired.
  induction Hpaired as [|origin row origins live Hin Htail [prior [Hprior Heq]]].
  - exists []. split; constructor.
  - apply in_map_iff in Hin as [[source original] [Hsame Hsource]].
    cbn [fst snd] in Hsame. inversion Hsame; subst source row.
    exists (original :: prior). split.
    + constructor; assumption.
    + cbn [map]. now f_equal.
Qed.

(** A mapped live row retains the source row paired with its origin label. *)
Lemma karr_pairs_map_lift : forall (f : list Z -> list Z)
    (pairs : list (list Z * list Z)) (origins live : list (list Z)),
  Forall2 (fun origin row => In (origin, row)
    (map (fun pair => (fst pair, f (snd pair))) pairs)) origins live ->
  exists prior,
    Forall2 (fun origin row => In (origin, row) pairs) origins prior /\
    live = map f prior.
Proof.
  intros f pairs origins live Hpaired.
  induction Hpaired as [|origin row origins live Hin Htail [prior [Hprior Heq]]].
  - exists []. split; constructor.
  - apply in_map_iff in Hin as [[source original] [Hsame Hsource]].
    cbn [fst snd] in Hsame. inversion Hsame; subst source row.
    exists (original :: prior). split.
    + constructor; assumption.
    + cbn [map]. now f_equal.
Qed.

(** Skipping a coordinate preserves every live minor equation. *)
Lemma karr_minor_law_skip : forall previous pivot_rows pivot_columns head columns pairs,
  karr_minor_law previous pivot_rows pivot_columns (head :: columns) pairs ->
  karr_minor_law previous pivot_rows pivot_columns columns
    (map (fun pair => (fst pair, karr_delete 0 (snd pair))) pairs).
Proof.
  intros previous pivot_rows pivot_columns head columns pairs Hlaw.
  unfold karr_minor_law in *. intros origins live selected Hpaired Hlength Hselected Hpositive.
  destruct (karr_pairs_delete_first_lift pairs origins live Hpaired)
    as [prior [Hprior Heq]]. subst live.
  rewrite karr_submatrix_delete_first.
  rewrite length_map in Hlength, Hpositive.
  assert (Hvalid : Forall (fun i => i < length (head :: columns)) (map S selected)).
  { apply Forall_forall. intros i Hi. apply in_map_iff in Hi as [j [Hj Hin]].
    subst i. pose proof (proj1 (Forall_forall _ _) Hselected j Hin) as Hj.
    cbn in Hj. cbn [length]. lia. }
  pose proof (Hlaw origins prior (map S selected) Hprior
    ltac:(rewrite length_map; exact Hlength) Hvalid ltac:(lia)) as Hstep.
  rewrite length_map in Hstep.
  rewrite map_map in Hstep. cbn [nth] in Hstep.
  rewrite !length_map. exact Hstep.
Qed.

(** Signed minors account for the row exchanges made when selecting a pivot. *)
Definition karr_signed_minors (width : nat) (rows : list (list Z)) : list Z :=
  flat_map (fun order =>
    flat_map (fun selected =>
      flat_map (fun columns =>
        let d := karr_determinant order (karr_submatrix columns selected) in
        match order with
        | 0 | 1 => [d]
        | S (S _) => [d; (-d)%Z]
        end)
        (karr_choose order (seq 0 width)))
      (karr_choose order rows))
    (seq 0 (S (Nat.min (length rows) width))).

TimeFun karr_signed_minors.

(** The order-zero minor is present for every source matrix. *)
Lemma karr_signed_minors_one : forall width rows,
  In 1%Z (karr_signed_minors width rows).
Proof.
  intros width rows. unfold karr_signed_minors.
  apply in_flat_map. exists 0. split; [apply in_seq; lia|].
  apply in_flat_map. exists []. split;
    [rewrite karr_choose_zero; now left|].
  apply in_flat_map. exists []. split;
    [rewrite karr_choose_zero; now left|].
  now left.
Qed.

(** The order-one determinant is its sole entry. *)
Lemma karr_determinant_one : forall z, karr_determinant 1 [[z]] = z.
Proof.
  intro z. cbn [karr_determinant karr_submatrix karr_delete karr_nth
    seq map fold_right Nat.even]. ring.
Qed.

(** A successful list lookup agrees with the dense integer accessor. *)
Lemma karr_nth_error_value : forall index row z,
  nth_error row index = Some z -> karr_nth index row = z.
Proof.
  induction index as [|index IH]; intros [|x row] z Hget;
    cbn [nth_error karr_nth] in *; try discriminate.
  - now injection Hget.
  - now apply IH.
Qed.

(** Every actual matrix entry is an independently enumerated order-one minor. *)
Lemma karr_signed_minors_entry : forall width rows row z,
  In row rows -> length row <= width -> In z row ->
  In z (karr_signed_minors width rows).
Proof.
  intros width rows row z Hrow Hwidth Hz.
  apply In_nth_error in Hz as [index Hget].
  assert (Hindex : index < length row).
  { apply nth_error_Some. rewrite Hget. discriminate. }
  assert (Hrows : 0 < length rows).
  { destruct rows; [contradiction|cbn; lia]. }
  assert (Horder : 1 <= Nat.min (length rows) width).
  { apply Nat.min_glb; lia. }
  unfold karr_signed_minors. apply in_flat_map. exists 1. split.
  - apply in_seq. lia.
  - apply in_flat_map. exists [row]. split.
    + rewrite karr_choose_one. apply in_map_iff. exists row. now split.
    + apply in_flat_map. exists [index]. split.
      * rewrite karr_choose_one. apply in_map_iff. exists index. split; [reflexivity|].
        apply in_seq. lia.
      * cbn [karr_submatrix map]. rewrite karr_determinant_one.
        rewrite (karr_nth_error_value _ _ _ Hget). now left.
Qed.

(** A selected singleton row and valid column give an order-one source minor. *)
Lemma karr_signed_minors_partition_one : forall width original row rest column,
  Permutation original (row :: rest) -> column < width ->
  In (karr_determinant 1 (karr_submatrix [column] [row]))
    (karr_signed_minors width original).
Proof.
  intros width original row rest column Hpartition Hcolumn.
  assert (Hrow : In row original).
  { eapply Permutation_in; [apply Permutation_sym; exact Hpartition|now left]. }
  assert (Hlength : 0 < length original).
  { destruct original; [contradiction|cbn [length]; lia]. }
  unfold karr_signed_minors. apply in_flat_map. exists 1. split.
  - apply in_seq. assert (Hmin : 1 <= Nat.min (length original) width)
      by (apply Nat.min_glb; lia). lia.
  - apply in_flat_map. exists [row]. split.
    + rewrite karr_choose_one. apply in_map_iff.
      exists row. split; [reflexivity|exact Hrow].
    + apply in_flat_map. exists [column]. split.
      * rewrite karr_choose_one. apply in_map_iff.
        exists column. split; [reflexivity|]. apply in_seq. lia.
      * now left.
Qed.

(** Every higher-order minor of selected rows occurs with its pivot-order sign. *)
Lemma karr_signed_minors_partition : forall width original selected rest columns,
  2 <= length selected -> length selected = length columns ->
  Permutation original (selected ++ rest) ->
  karr_increasing columns ->
  Forall (fun column => column < width) columns ->
  In (karr_determinant (length selected) (karr_submatrix columns selected))
    (karr_signed_minors width original).
Proof.
  intros width original selected rest columns Horder Hsquare Hpartition
    Hincreasing Hbound.
  destruct (karr_choose_partition original selected rest Hpartition)
    as [ordered [Hordered Hperm]].
  assert (Hcolumns : In columns
      (karr_choose (length columns) (seq 0 width))).
  { apply karr_choose_seq_increasing; [exact Hincreasing|].
    eapply Forall_impl; [|exact Hbound].
    intros column Hcolumn. cbn in Hcolumn. lia. }
  assert (Hcolumn_count : length columns <= width).
  { pose proof (karr_choose_count_le nat (seq 0 width)
      (length columns) columns Hcolumns) as Hcount.
    now rewrite length_seq in Hcount. }
  assert (Hrow_count : length selected <= length original).
  { pose proof (Permutation_length Hpartition) as Hcount.
    rewrite length_app in Hcount. lia. }
  assert (Hselected_perm : Permutation
      (karr_submatrix columns selected) (karr_submatrix columns ordered)).
  { unfold karr_submatrix. apply Permutation_map.
    now apply Permutation_sym. }
  destruct (length selected) as [|[|order]] eqn:Hrows; try lia.
  destruct (karr_determinant_permutation _ _ Hselected_perm
    (S order) [] [] (length columns)
    ltac:(unfold karr_submatrix; rewrite length_map; cbn [length];
      rewrite Hrows; lia)
    (karr_submatrix_width columns selected)) as [sign [Hsign Hdet]].
  cbn [app] in Hdet. rewrite !app_nil_r in Hdet.
  unfold karr_signed_minors. apply in_flat_map.
  exists (S (S order)). split.
  - apply in_seq.
    assert (Hmin : S (S order) <= Nat.min (length original) width)
      by (apply Nat.min_glb; lia).
    lia.
  - apply in_flat_map. exists ordered. split.
    + exact Hordered.
    + apply in_flat_map. exists columns. split.
      * rewrite <- Hsquare in Hcolumns. exact Hcolumns.
      * cbn [length]. destruct Hsign as [Hsign|Hsign].
        -- left. rewrite Hdet, Hsign. ring.
        -- right. left. rewrite Hdet, Hsign. ring.
Qed.

(** A live augmented entry represented by the minor law is a signed source minor. *)
Lemma karr_minor_law_entry : forall previous pivot_rows pivot_columns columns
    pairs original width origin live z,
  karr_minor_law previous pivot_rows pivot_columns columns pairs ->
  Permutation original (pivot_rows ++ map fst pairs) ->
  karr_increasing (pivot_columns ++ columns) ->
  Forall (fun column => column < width) (pivot_columns ++ columns) ->
  length pivot_rows = length pivot_columns ->
  length live = length columns -> In (origin, live) pairs -> In z live ->
  In z (karr_signed_minors width original).
Proof.
  intros previous pivot_rows pivot_columns columns pairs original width
    origin live z Hlaw Hpartition Hincreasing Hbound Hsquare Hlive Hpair Hz.
  apply In_nth_error in Hz as [index Hget].
  assert (Hindex : index < length columns).
  { rewrite <- Hlive. apply nth_error_Some. rewrite Hget. discriminate. }
  set (column := nth index columns 0%nat).
  assert (Hmember : In column columns).
  { unfold column. now apply karr_nth_list_member. }
  assert (Horigin : In origin (map fst pairs)).
  { apply in_map_iff. exists (origin, live). now split. }
  destruct (karr_partition_select _ original pivot_rows (map fst pairs)
    origin Hpartition Horigin) as [rest Hselected_rows].
  assert (Hselected_columns : karr_increasing (pivot_columns ++ [column])).
  { now apply karr_increasing_prefix_member with (suffix := columns). }
  assert (Hselected_bound : Forall (fun c => c < width) (pivot_columns ++ [column])).
  { apply Forall_app in Hbound as [Hprefix Htail].
    apply Forall_app. split; [exact Hprefix|].
    constructor; [exact (proj1 (Forall_forall _ _) Htail column Hmember)|constructor]. }
  assert (Hpaired : Forall2 (fun source row => In (source, row) pairs)
    [origin] [live]) by (constructor; [exact Hpair|constructor]).
  assert (Hvalid : Forall (fun i => i < length columns) [index])
    by (constructor; [exact Hindex|constructor]).
  unfold karr_minor_law in Hlaw.
  pose proof (Hlaw [origin] [live] [index] Hpaired eq_refl Hvalid
    ltac:(cbn [length]; lia)) as Hminor.
  cbn [length karr_submatrix map Nat.sub Nat.add] in Hminor.
  rewrite karr_determinant_one, Z.pow_0_r, Z.mul_1_l in Hminor.
  rewrite (karr_nth_error_value _ _ _ Hget) in Hminor.
  replace (length pivot_rows + 1) with (S (length pivot_rows)) in Hminor by lia.
  fold column in Hminor.
  change (z = karr_determinant (S (length pivot_rows))
    (karr_submatrix (pivot_columns ++ [column]) (pivot_rows ++ [origin])))
    in Hminor.
  rewrite Hminor.
  destruct pivot_rows as [|first remaining].
  - destruct pivot_columns as [|c pivot_columns];
      [|cbn [length] in Hsquare; lia].
    cbn [app length] in Hselected_rows, Hselected_columns, Hselected_bound |- *.
    apply karr_signed_minors_partition_one with (rest := rest).
    + exact Hselected_rows.
    + exact (proj1 (Forall_forall _ _) Hselected_bound column (or_introl eq_refl)).
  - replace (S (length (first :: remaining))) with
      (length ((first :: remaining) ++ [origin]))
      by (rewrite length_app; cbn [length]; lia).
    apply karr_signed_minors_partition with (rest := rest).
    + rewrite length_app. cbn [length]. lia.
    + rewrite !length_app. cbn [length] in Hsquare |- *. lia.
    + exact Hselected_rows.
    + exact Hselected_columns.
    + exact Hselected_bound.
Qed.

(** The traced run carries labels, widths, a nonzero prior minor and every-order equations. *)
Definition karr_run_state (width cols : nat) (original : list (list Z))
    (previous : Z) (pivot_rows : list (list Z))
    (pivot_columns columns : list nat) (labels : list (list Z))
    (rows : list karr_row) : Prop :=
  previous <> 0%Z /\
  previous = karr_determinant (length pivot_rows)
    (karr_submatrix pivot_columns pivot_rows) /\
  length labels = length rows /\
  Forall (fun row => length (kcoeff row) = cols) rows /\
  Forall (fun row => length (karr_row_entries row) = length columns) rows /\
  cols <= length columns /\
  length pivot_rows = length pivot_columns /\
  Permutation original (pivot_rows ++ labels) /\
  karr_increasing (pivot_columns ++ columns) /\
  Forall (fun column => column < width) (pivot_columns ++ columns) /\
  karr_minor_law previous pivot_rows pivot_columns columns
    (combine labels (map karr_row_entries rows)).

(** Removing the coefficient head maps each paired augmented row to its tail. *)
Lemma karr_pairs_tail : forall cols (labels : list (list Z)) (rows : list karr_row),
  length labels = length rows ->
  Forall (fun row => length (kcoeff row) = S cols) rows ->
  combine labels (map karr_row_entries (map karr_tail rows)) =
    map (fun pair => (fst pair, karr_delete 0 (snd pair)))
      (combine labels (map karr_row_entries rows)).
Proof.
  intros cols labels. induction labels as [|label labels IH];
    intros [|row rows] Hlength Hcoeff; cbn [length] in Hlength;
    try discriminate; [reflexivity|].
  apply Forall_cons_iff in Hcoeff as [Hrow Hrows].
  cbn [map combine]. f_equal.
  - rewrite karr_row_entries_tail.
    + reflexivity.
    + destruct (kcoeff row) as [|z coeff] eqn:Hnonempty;
        cbn [length] in Hrow; [lia|discriminate].
  - apply IH; [lia|exact Hrows].
Qed.

(** A skipped pivot column preserves the concrete labeled run invariant. *)
Lemma karr_run_state_skip : forall width cols original previous pivot_rows
    pivot_columns head columns labels rows,
  karr_run_state width (S cols) original previous pivot_rows pivot_columns
    (head :: columns) labels rows ->
  karr_run_state width cols original previous pivot_rows pivot_columns
    columns labels (map karr_tail rows).
Proof.
  intros width cols original previous pivot_rows pivot_columns head columns
    labels rows Hstate.
  unfold karr_run_state in *. destruct Hstate as
    [Hprevious [Hdet [Hlabels [Hcoeff [Hentries [Hcolumns [Hsquare
      [Hpartition [Hincreasing [Hbounded Hlaw]]]]]]]]]].
  repeat split.
  - exact Hprevious.
  - exact Hdet.
  - now rewrite length_map.
  - apply Forall_forall. intros r Hin.
    apply in_map_iff in Hin as [source [Heq Hsource]]. subst r.
    pose proof (proj1 (Forall_forall _ _) Hcoeff source Hsource) as Hsource_coeff.
    destruct source as [coeff right weight scale].
    cbn [karr_tail kcoeff] in *. destruct coeff as [|z coeff];
      cbn [length tl] in *; lia.
  - apply Forall_forall. intros r Hin.
    apply in_map_iff in Hin as [source [Heq Hsource]]. subst r.
    pose proof (proj1 (Forall_forall _ _) Hcoeff source Hsource) as Hsource_coeff.
    pose proof (proj1 (Forall_forall _ _) Hentries source Hsource) as Hsource_entries.
    destruct source as [coeff right weight scale].
    destruct coeff as [|z coeff]; cbn [kcoeff length] in Hsource_coeff; [lia|].
    unfold karr_row_entries in *. cbn [karr_tail kcoeff kright kweight kscale] in *.
    rewrite !length_app in *. cbn [tl length] in *. lia.
  - cbn [length] in Hcolumns |- *. lia.
  - exact Hsquare.
  - exact Hpartition.
  - now apply karr_increasing_skip with (head := head).
  - apply Forall_app in Hbounded as [Hprefix Htail].
    apply Forall_cons_iff in Htail as [_ Hrest].
    apply Forall_app. now split.
  - rewrite (karr_pairs_tail cols labels rows Hlabels Hcoeff).
    now apply karr_minor_law_skip with (head := head).
Qed.

(** A certificate unit vector has the declared source-row width. *)
Lemma karr_unit_length : forall total index, length (karr_unit total index) = total.
Proof.
  induction total as [|total IH]; intros [|index]; cbn [karr_unit length];
    try reflexivity.
  - now rewrite repeat_length.
  - now rewrite IH.
Qed.

(** The order-two determinant has the usual cross-product formula. *)
Lemma karr_determinant_two : forall a b c d,
  karr_determinant 2 [[a; b]; [c; d]] = (a * d - b * c)%Z.
Proof.
  intros a b c d. cbn [karr_determinant karr_delete karr_nth seq map fold_right
    Nat.even]. ring.
Qed.

(** The order-two law makes every undivided pivot cross divisible by the prior minor. *)
Lemma karr_minor_law_cross_divisible : forall previous pivot_rows pivot_columns
    head columns pairs pivot_origin pivot target_origin target index,
  karr_minor_law previous pivot_rows pivot_columns (head :: columns) pairs ->
  previous <> 0%Z ->
  In (pivot_origin, pivot) pairs -> In (target_origin, target) pairs ->
  length pivot = length (head :: columns) -> length target = length pivot ->
  index < length target ->
  (karr_nth index
    (karr_cross (karr_nth 0 pivot) (karr_nth 0 target) target pivot)
      mod previous = 0)%Z.
Proof.
  intros previous pivot_rows pivot_columns head columns pairs
    pivot_origin pivot target_origin target [|index] Hlaw Hprevious
    Hpivot Htarget Hpivot_width Htarget_width Hindex.
  - rewrite karr_nth_cross by lia.
    replace (karr_nth 0 pivot * karr_nth 0 target -
      karr_nth 0 target * karr_nth 0 pivot)%Z with 0%Z by ring.
    apply Z.mod_0_l. exact Hprevious.
  - assert (Hvalid : Forall (fun i => i < length (head :: columns)) [0; S index]).
    { constructor; [cbn [length] in *; lia|].
      constructor; [cbn [length] in *; lia|constructor]. }
    assert (Hpaired : Forall2 (fun origin row => In (origin, row) pairs)
      [pivot_origin; target_origin] [pivot; target]).
    { repeat constructor; assumption. }
    unfold karr_minor_law in Hlaw.
    pose proof (Hlaw [pivot_origin; target_origin] [pivot; target]
      [0; S index] Hpaired eq_refl Hvalid ltac:(cbn [length]; lia)) as Hdet.
    cbn [length karr_submatrix map Nat.sub Nat.add] in Hdet.
    rewrite karr_determinant_two in Hdet.
    rewrite Z.pow_1_r in Hdet.
    rewrite karr_nth_cross by lia.
    replace (karr_nth 0 target * karr_nth (S index) pivot)%Z with
      (karr_nth (S index) pivot * karr_nth 0 target)%Z by ring.
    rewrite Hdet. rewrite Z.mul_comm. apply Z.mod_mul. exact Hprevious.
Qed.

(** The selected pivot value is the next bordered minor. *)
Lemma karr_minor_law_pivot_value : forall previous pivot_rows pivot_columns
    head columns pairs origin pivot,
  karr_minor_law previous pivot_rows pivot_columns (head :: columns) pairs ->
  In (origin, pivot) pairs ->
  karr_nth 0 pivot =
    karr_determinant (S (length pivot_rows))
      (karr_submatrix (pivot_columns ++ [head]) (pivot_rows ++ [origin])).
Proof.
  intros previous pivot_rows pivot_columns head columns pairs origin pivot Hlaw Hin.
  unfold karr_minor_law in Hlaw.
  assert (Hpaired : Forall2 (fun source row => In (source, row) pairs)
    [origin] [pivot]) by (constructor; [exact Hin|constructor]).
  assert (Hvalid : Forall (fun i => i < length (head :: columns)) [0])
    by (constructor; [cbn [length]; lia|constructor]).
  pose proof (Hlaw [origin] [pivot] [0] Hpaired eq_refl Hvalid
    ltac:(cbn [length]; lia)) as Hminor.
  cbn [length karr_submatrix map nth Nat.sub Nat.add] in Hminor.
  rewrite karr_determinant_one, Z.pow_0_r in Hminor.
  replace (length pivot_rows + 1) with (S (length pivot_rows)) in Hminor by lia.
  rewrite Z.mul_1_l in Hminor. exact Hminor.
Qed.

(** The all-order law selects the exact quotient branch for an augmented row. *)
Lemma karr_minor_law_reduce_exact : forall previous pivot_rows pivot_columns
    head columns pairs pivot_origin target_origin p r,
  karr_minor_law previous pivot_rows pivot_columns (head :: columns) pairs ->
  previous <> 0%Z ->
  In (pivot_origin, karr_row_entries p) pairs ->
  In (target_origin, karr_row_entries r) pairs ->
  length (kcoeff p) = length (kcoeff r) ->
  length (kweight p) = length (kweight r) ->
  kcoeff p <> [] -> kcoeff r <> [] ->
  length (karr_row_entries p) = length (head :: columns) ->
  length (karr_row_entries r) = length (karr_row_entries p) ->
  karr_exact previous (KRow
    (karr_cross (karr_head p) (karr_head r) (kcoeff r) (kcoeff p))
    (karr_head p * kright r - karr_head r * kright p)%Z
    (karr_cross (karr_head p) (karr_head r) (kweight r) (kweight p))
    (karr_head p * kscale r - karr_head r * kscale p)%Z) = true.
Proof.
  intros previous pivot_rows pivot_columns head columns pairs pivot_origin
    target_origin p r Hlaw Hprevious Hpivot Htarget Hcoeff Hweight
    Hp_nonempty Hr_nonempty Hp_width Hr_width.
  apply karr_exact_from_entries; [exact Hprevious|].
  intros z Hin.
  rewrite karr_row_entries_cross in Hin by (symmetry; assumption).
  rewrite <- (karr_row_entries_head p Hp_nonempty) in Hin.
  rewrite <- (karr_row_entries_head r Hr_nonempty) in Hin.
  apply In_nth_error in Hin as [index Hget].
  assert (Hindex : index < length (karr_row_entries r)).
  { assert (Hcross_index : index < length (karr_cross
        (karr_nth 0 (karr_row_entries p))
        (karr_nth 0 (karr_row_entries r))
        (karr_row_entries r) (karr_row_entries p))).
    { apply nth_error_Some. rewrite Hget. discriminate. }
    rewrite karr_cross_length in Hcross_index by exact Hr_width.
    exact Hcross_index. }
  pose proof (karr_minor_law_cross_divisible previous pivot_rows pivot_columns
    head columns pairs pivot_origin (karr_row_entries p) target_origin
    (karr_row_entries r) index Hlaw Hprevious Hpivot Htarget
    Hp_width Hr_width Hindex) as Hmod.
  rewrite (karr_nth_error_value _ _ _ Hget) in Hmod. exact Hmod.
Qed.

(** Exact pivot reduction realizes the row quotient required by the minor law. *)
Lemma karr_minor_law_reduce_multiple : forall previous pivot_rows pivot_columns
    head columns pairs pivot_origin target_origin p r,
  karr_minor_law previous pivot_rows pivot_columns (head :: columns) pairs ->
  previous <> 0%Z ->
  In (pivot_origin, karr_row_entries p) pairs ->
  In (target_origin, karr_row_entries r) pairs ->
  length (kcoeff p) = length (kcoeff r) ->
  length (kweight p) = length (kweight r) ->
  kcoeff p <> [] -> kcoeff r <> [] ->
  length (karr_row_entries p) = length (head :: columns) ->
  length (karr_row_entries r) = length (karr_row_entries p) ->
  map (fun z => (previous * z)%Z)
    (karr_row_entries (karr_reduce previous (karr_head p) (karr_head r) p r)) =
  karr_cross (karr_head p) (karr_head r)
    (karr_row_entries r) (karr_row_entries p).
Proof.
  intros previous pivot_rows pivot_columns head columns pairs pivot_origin
    target_origin p r Hlaw Hprevious Hpivot Htarget Hcoeff Hweight
    Hp_nonempty Hr_nonempty Hp_width Hr_width.
  eapply karr_row_entries_reduce_multiple.
  - symmetry. exact Hcoeff.
  - symmetry. exact Hweight.
  - exact Hprevious.
  - eapply karr_minor_law_reduce_exact; eauto.
  - intros z Hin.
    rewrite <- (karr_row_entries_head p Hp_nonempty) in Hin.
    rewrite <- (karr_row_entries_head r Hr_nonempty) in Hin.
    apply In_nth_error in Hin as [index Hget].
    assert (Hindex : index < length (karr_row_entries r)).
    { assert (Hcross_index : index < length (karr_cross
          (karr_nth 0 (karr_row_entries p))
          (karr_nth 0 (karr_row_entries r))
          (karr_row_entries r) (karr_row_entries p))).
      { apply nth_error_Some. rewrite Hget. discriminate. }
      rewrite karr_cross_length in Hcross_index by exact Hr_width.
      exact Hcross_index. }
    pose proof (karr_minor_law_cross_divisible previous pivot_rows pivot_columns
      head columns pairs pivot_origin (karr_row_entries p) target_origin
      (karr_row_entries r) index Hlaw Hprevious Hpivot Htarget
      Hp_width Hr_width Hindex) as Hmod.
    rewrite (karr_nth_error_value _ _ _ Hget) in Hmod. exact Hmod.
Qed.

(** The order-three determinant agrees with the six signed permutation products. *)
Lemma karr_determinant_three : forall a b c d e f g h i,
  karr_determinant 3 [[a; b; c]; [d; e; f]; [g; h; i]] =
    (a * e * i + b * f * g + c * d * h - c * e * g - b * d * i - a * f * h)%Z.
Proof.
  intros a b c d e f g h i. cbn [karr_determinant karr_delete karr_nth seq map fold_right
    Nat.even]. ring.
Qed.

(** The first nontrivial Bareiss division is the three-row Sylvester identity. *)
Lemma karr_sylvester_three : forall a b c d e f g h i,
  ((a * e - b * d) * (a * i - c * g) -
    (a * f - c * d) * (a * h - b * g))%Z =
    (a * karr_determinant 3 [[a; b; c]; [d; e; f]; [g; h; i]])%Z.
Proof.
  intros a b c d e f g h i. rewrite karr_determinant_three. ring.
Qed.

(** Dividing the three-row cross product by a nonzero first pivot is exact. *)
Lemma karr_sylvester_three_quotient : forall a b c d e f g h i,
  a <> 0%Z ->
  (((a * e - b * d) * (a * i - c * g) -
    (a * f - c * d) * (a * h - b * g)) / a)%Z =
    karr_determinant 3 [[a; b; c]; [d; e; f]; [g; h; i]].
Proof.
  intros a b c d e f g h i Hnonzero. rewrite karr_sylvester_three, Z.mul_comm.
  now apply Z.div_mul.
Qed.

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

(** Shared coefficient and augmented widths determine the multiplier width. *)
Lemma karr_weight_width_of_entries : forall p r,
  length (kcoeff p) = length (kcoeff r) ->
  length (karr_row_entries p) = length (karr_row_entries r) ->
  length (kweight p) = length (kweight r).
Proof.
  intros p r Hcoeff Hentries.
  unfold karr_row_entries in Hentries. rewrite !length_app in Hentries.
  cbn [length] in Hentries. rewrite !length_app in Hentries.
  cbn [length] in Hentries. lia.
Qed.

(** Guarded division preserves the full augmented row width in either branch. *)
Lemma karr_divide_entries_width : forall d r,
  length (karr_row_entries (karr_divide d r)) = length (karr_row_entries r).
Proof.
  intros d r. unfold karr_divide. destruct (karr_exact d r);
    [rewrite karr_row_entries_quotient, length_map|]; reflexivity.
Qed.

(** A reduction of equally wide rows keeps their augmented width. *)
Lemma karr_reduce_entries_width : forall d a b p r,
  length (kcoeff r) = length (kcoeff p) ->
  length (kweight r) = length (kweight p) ->
  length (karr_row_entries (karr_reduce d a b p r)) =
    length (karr_row_entries r).
Proof.
  intros d a b p r Hcoeff Hweight. unfold karr_reduce.
  rewrite karr_divide_entries_width.
  rewrite karr_row_entries_cross by assumption.
  apply karr_cross_length.
  unfold karr_row_entries. rewrite !length_app.
  cbn [length]. rewrite !length_app. cbn [length]. lia.
Qed.

(** Dropping a leading coordinate reduces a positive width by one. *)
Lemma karr_tail_width : forall n r, length (kcoeff r) = S n ->
  length (kcoeff (karr_tail r)) = n.
Proof.
  intros n [zs rhs ws sc] Hwidth; cbn [kcoeff karr_tail] in *.
  destruct zs; cbn [length tl] in *; lia.
Qed.

(** The reduced tail is the quotient of the crossed augmented row without its head. *)
Lemma karr_reduced_tail_entries : forall cols d a b p r,
  length (kcoeff p) = S cols ->
  length (kcoeff r) = S cols ->
  length (kweight r) = length (kweight p) ->
  karr_exact d (KRow (karr_cross a b (kcoeff r) (kcoeff p))
    (a * kright r - b * kright p)%Z
    (karr_cross a b (kweight r) (kweight p))
    (a * kscale r - b * kscale p)%Z) = true ->
  karr_row_entries (karr_tail (karr_reduce d a b p r)) =
    karr_delete 0
      (map (fun z => (z / d)%Z)
        (karr_cross a b (karr_row_entries r) (karr_row_entries p))).
Proof.
  intros cols d a b p r Hp Hr Hweight Hexact.
  rewrite karr_row_entries_tail.
  - rewrite karr_row_entries_reduce_exact; [reflexivity|lia|exact Hweight|exact Hexact].
  - pose proof (karr_reduce_width d a b p r ltac:(lia)) as Hwidth.
    rewrite Hr in Hwidth. destruct (kcoeff (karr_reduce d a b p r));
      cbn [length] in Hwidth; discriminate.
Qed.

(** Entrywise equality transports a paired label list through a row operation. *)
Lemma karr_pairs_map_rows : forall (labels : list (list Z))
    (rows : list karr_row) (g : karr_row -> karr_row)
    (f : list Z -> list Z),
  length labels = length rows ->
  (forall row, In row rows -> karr_row_entries (g row) = f (karr_row_entries row)) ->
  combine labels (map karr_row_entries (map g rows)) =
    map (fun pair => (fst pair, f (snd pair)))
      (combine labels (map karr_row_entries rows)).
Proof.
  intros labels. induction labels as [|label labels IH];
    intros [|row rows] g f Hlength Heq; cbn [length] in Hlength;
    try discriminate; [reflexivity|].
  cbn [map combine fst snd]. f_equal.
  - f_equal. apply Heq. now left.
  - apply IH; [lia|]. intros source Hin. apply Heq. now right.
Qed.

(** A paired origin and entry vector comes from one concrete augmented row. *)
Lemma karr_pair_entries_member : forall (labels : list (list Z))
    (rows : list karr_row) origin entries,
  In (origin, entries) (combine labels (map karr_row_entries rows)) ->
  exists row, In row rows /\ entries = karr_row_entries row.
Proof.
  intros labels. induction labels as [|label labels IH];
    intros [|row rows] origin entries Hin; cbn [map combine] in Hin;
    try contradiction.
  destruct Hin as [Heq|Hin].
  - inversion Heq; subst. exists row. split; [now left|reflexivity].
  - destruct (IH rows origin entries Hin) as [source [Hsource Heq]].
    exists source. split; [now right|exact Heq].
Qed.

(** Each row in aligned lists keeps some origin label in their pairing. *)
Lemma karr_pair_entries_origin : forall (labels : list (list Z))
    (rows : list karr_row) row,
  length labels = length rows -> In row rows ->
  exists origin, In (origin, karr_row_entries row)
    (combine labels (map karr_row_entries rows)).
Proof.
  intros labels. induction labels as [|label labels IH];
    intros [|source rows] row Hlength Hin; cbn [length] in Hlength;
    try discriminate; try contradiction.
  cbn [map combine]. destruct Hin as [Heq|Hin].
  - subst row. exists label. now left.
  - destruct (IH rows row ltac:(lia) Hin) as [origin Horigin].
    exists origin. now right.
Qed.

(** Deleting the first coordinate commutes with an entrywise map. *)
Lemma karr_delete_map_first : forall (f : Z -> Z) xs,
  karr_delete 0 (map f xs) = map f (karr_delete 0 xs).
Proof.
  intros f [|x xs]; reflexivity.
Qed.

(** The exact reduced tail scales back to the crossed row without its head. *)
Lemma karr_reduced_tail_multiple : forall cols d a b p r,
  length (kcoeff p) = S cols ->
  length (kcoeff r) = S cols ->
  length (kweight r) = length (kweight p) ->
  d <> 0%Z ->
  karr_exact d (KRow (karr_cross a b (kcoeff r) (kcoeff p))
    (a * kright r - b * kright p)%Z
    (karr_cross a b (kweight r) (kweight p))
    (a * kscale r - b * kscale p)%Z) = true ->
  (forall z, In z (karr_cross a b (karr_row_entries r) (karr_row_entries p)) ->
    (z mod d = 0)%Z) ->
  map (fun z => (d * z)%Z)
    (karr_row_entries (karr_tail (karr_reduce d a b p r))) =
    karr_delete 0 (karr_cross a b
      (karr_row_entries r) (karr_row_entries p)).
Proof.
  intros cols d a b p r Hp Hr Hweight Hd Hexact Hmultiple.
  rewrite karr_row_entries_tail.
  - rewrite <- karr_delete_map_first.
    rewrite karr_row_entries_reduce_multiple;
      [reflexivity|lia|exact Hweight|exact Hd|exact Hexact|exact Hmultiple].
  - pose proof (karr_reduce_width d a b p r ltac:(lia)) as Hwidth.
    rewrite Hr in Hwidth. destruct (kcoeff (karr_reduce d a b p r));
      cbn [length] in Hwidth; discriminate.
Qed.

(** Under the minor law, an actual pivot tail has the scaled stage equation. *)
Lemma karr_minor_law_reduced_tail : forall cols previous pivot_rows
    pivot_columns head columns pairs pivot_origin target_origin p r,
  karr_minor_law previous pivot_rows pivot_columns (head :: columns) pairs ->
  previous <> 0%Z ->
  In (pivot_origin, karr_row_entries p) pairs ->
  In (target_origin, karr_row_entries r) pairs ->
  length (kcoeff p) = S cols -> length (kcoeff r) = S cols ->
  length (karr_row_entries p) = length (head :: columns) ->
  length (karr_row_entries r) = length (head :: columns) ->
  map (fun z => (previous * z)%Z)
    (karr_row_entries
      (karr_tail (karr_reduce previous (karr_head p) (karr_head r) p r))) =
    karr_delete 0
      (karr_cross (karr_nth 0 (karr_row_entries p))
        (karr_nth 0 (karr_row_entries r))
        (karr_row_entries r) (karr_row_entries p)).
Proof.
  intros cols previous pivot_rows pivot_columns head columns pairs
    pivot_origin target_origin p r Hlaw Hprevious Hpivot Htarget
    Hp_coeff Hr_coeff Hp_entries Hr_entries.
  assert (Hweight : length (kweight p) = length (kweight r)).
  { apply karr_weight_width_of_entries; lia. }
  assert (Hstep : map (fun z => (previous * z)%Z)
    (karr_row_entries
      (karr_reduce previous (karr_head p) (karr_head r) p r)) =
    karr_cross (karr_head p) (karr_head r)
      (karr_row_entries r) (karr_row_entries p)).
  { eapply karr_minor_law_reduce_multiple; eauto; try lia.
    - destruct (kcoeff p); cbn [length] in Hp_coeff; discriminate.
    - destruct (kcoeff r); cbn [length] in Hr_coeff; discriminate. }
  rewrite karr_row_entries_tail.
  - rewrite <- karr_delete_map_first, Hstep.
    rewrite (karr_row_entries_head p), (karr_row_entries_head r);
      [reflexivity| |].
    + destruct (kcoeff r) as [|z coeff];
        [cbn [length] in Hr_coeff; lia|intros H; discriminate].
    + destruct (kcoeff p) as [|z coeff];
        [cbn [length] in Hp_coeff; lia|intros H; discriminate].
  - pose proof (karr_reduce_width previous (karr_head p) (karr_head r) p r
      ltac:(lia)) as Hwidth.
    rewrite Hr_coeff in Hwidth.
    destruct (kcoeff (karr_reduce previous (karr_head p) (karr_head r) p r));
      cbn [length] in Hwidth; discriminate.
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

(** Column selection commutes with uniform row scaling. *)
Lemma karr_submatrix_scale : forall d columns rows,
  karr_submatrix columns (map (map (fun z => (d * z)%Z)) rows) =
    map (map (fun z => (d * z)%Z)) (karr_submatrix columns rows).
Proof.
  intros d columns rows. unfold karr_submatrix. rewrite !map_map.
  apply map_ext. intro row. rewrite map_map.
  apply map_ext. intro index. now rewrite karr_nth_scale.
Qed.

(** Scaling selected rows multiplies every minor by one factor per row. *)
Lemma karr_submatrix_scale_minor : forall d columns rows,
  karr_determinant (length rows)
    (karr_submatrix columns (map (map (fun z => (d * z)%Z)) rows)) =
  (d ^ Z.of_nat (length rows) *
    karr_determinant (length rows) (karr_submatrix columns rows))%Z.
Proof.
  intros d columns rows. rewrite karr_submatrix_scale.
  replace (length rows) with (length (karr_submatrix columns rows))
    by (unfold karr_submatrix; now rewrite length_map).
  pose proof (karr_determinant_scale_rows
    (length (karr_submatrix columns rows)) [] (karr_submatrix columns rows) [] d
    ltac:(cbn [length]; lia)) as Hscale.
  cbn [app] in Hscale. rewrite !app_nil_r in Hscale. exact Hscale.
Qed.

(** Coordinatewise exact quotients scale every selected determinant uniformly. *)
Lemma karr_submatrix_multiple_minor : forall d columns quotients raw,
  Forall2 (fun q r => map (fun z => (d * z)%Z) q = r) quotients raw ->
  karr_determinant (length raw) (karr_submatrix columns raw) =
    (d ^ Z.of_nat (length quotients) *
      karr_determinant (length quotients) (karr_submatrix columns quotients))%Z.
Proof.
  intros d columns quotients raw Hmultiple.
  assert (Hraw : raw = map (map (fun z => (d * z)%Z)) quotients).
  { induction Hmultiple as [|q r qs rs Hhead Htail IH];
      cbn [map]; [reflexivity|]. now rewrite <- Hhead, IH. }
  subst raw. rewrite length_map. apply karr_submatrix_scale_minor.
Qed.

(** Uniform exact row quotients transfer the full stage identity. *)
Lemma karr_stage_quotient_minor : forall d p xs ys quotients,
  karr_nth 0 p <> 0%Z ->
  Forall (fun x => length x = length p) xs ->
  length ys = length xs -> 1 <= length xs ->
  Forall2 (fun q x =>
    map (fun z => (d * z)%Z) q =
      karr_delete 0 (karr_cross (karr_nth 0 p) (karr_nth 0 x) x p))
    quotients xs ->
  (d ^ Z.of_nat (length xs) *
    karr_determinant (length ys) (karr_submatrix ys quotients) =
   karr_nth 0 p ^ Z.of_nat (length xs - 1) *
    karr_determinant (S (length ys))
      (karr_submatrix (0%nat :: map S ys) (p :: xs)))%Z.
Proof.
  intros d p xs ys quotients Hp Hwidth Hlength Hpositive Hquotients.
  pose proof (Forall2_length Hquotients) as Hrows.
  pose proof (karr_stage_minor 0 p xs (map S ys) Hp Hwidth
    ltac:(rewrite length_map; exact Hlength) Hpositive) as Hstage.
  rewrite length_map in Hstage.
  rewrite <- karr_submatrix_delete_first in Hstage.
  assert (Hraw : map (karr_delete 0)
      (map (fun x => karr_cross (karr_nth 0 p) (karr_nth 0 x) x p) xs) =
    map (map (fun z => (d * z)%Z)) quotients).
  { clear Hrows Hstage Hwidth Hlength Hpositive Hp.
    induction Hquotients as [|q x quotients xs Hhead Htail IH];
      cbn [map]; [reflexivity|].
    f_equal; [symmetry; exact Hhead|exact IH]. }
  rewrite Hraw in Hstage.
  replace (length ys) with (length quotients) in Hstage by lia.
  rewrite karr_submatrix_scale_minor in Hstage.
  rewrite Hrows in Hstage. rewrite Hlength. exact Hstage.
Qed.

(** A nonzero pivot and exact row quotients preserve all live minor equations. *)
Lemma karr_minor_law_pivot : forall previous pivot_rows pivot_columns head columns
    pivot_origin pivot rest (f : list Z -> list Z),
  karr_minor_law previous pivot_rows pivot_columns (head :: columns)
    ((pivot_origin, pivot) :: rest) ->
  previous <> 0%Z -> karr_nth 0 pivot <> 0%Z ->
  (forall origin row, In (origin, row) rest -> length row = length pivot) ->
  (forall origin row, In (origin, row) rest ->
    map (fun z => (previous * z)%Z) (f row) =
      karr_delete 0
        (karr_cross (karr_nth 0 pivot) (karr_nth 0 row) row pivot)) ->
  karr_minor_law (karr_nth 0 pivot) (pivot_rows ++ [pivot_origin])
    (pivot_columns ++ [head]) columns
    (map (fun pair => (fst pair, f (snd pair))) rest).
Proof.
  intros previous pivot_rows pivot_columns head columns pivot_origin pivot rest f
    Hlaw Hprevious Hp Hwidth Hquotient.
  unfold karr_minor_law in *. intros origins quotients selected
    Hpaired Hlength Hselected Hpositive.
  destruct (karr_pairs_map_lift f rest origins quotients Hpaired)
    as [live [Hlive Heq]]. subst quotients.
  rewrite length_map in Hlength, Hpositive.
  assert (Hlive_width : Forall (fun row => length row = length pivot) live).
  { clear Hpaired Hlength Hselected Hpositive.
    induction Hlive as [|origin row origins live Hin Htail IH];
      [constructor|constructor; [now apply Hwidth with (origin := origin)|exact IH]]. }
  assert (Hlive_quotient : Forall2 (fun q row =>
      map (fun z => (previous * z)%Z) q =
        karr_delete 0
          (karr_cross (karr_nth 0 pivot) (karr_nth 0 row) row pivot))
      (map f live) live).
  { clear Hpaired Hlength Hselected Hpositive Hlive_width.
    induction Hlive as [|origin row origins live Hin Htail IH];
      cbn [map]; [constructor|].
    constructor; [now apply Hquotient with (origin := origin)|exact IH]. }
  assert (Hcurrent : Forall2
      (fun origin row => In (origin, row) ((pivot_origin, pivot) :: rest))
      (pivot_origin :: origins) (pivot :: live)).
  { constructor; [now left|].
    eapply Forall2_impl; [|exact Hlive]. intros origin row Hin. now right. }
  assert (Hvalid : Forall (fun i => i < length (head :: columns))
      (0 :: map S selected)).
  { constructor; [cbn [length]; lia|].
    apply Forall_forall. intros i Hi.
    apply in_map_iff in Hi as [j [Hj Hin]]. subst i.
    pose proof (proj1 (Forall_forall _ _) Hselected j Hin) as Hjvalid.
    cbn in Hjvalid. cbn [length]. lia. }
  pose proof (Hlaw (pivot_origin :: origins) (pivot :: live)
    (0 :: map S selected) Hcurrent
    ltac:(cbn [length]; rewrite length_map; lia) Hvalid
    ltac:(cbn [length]; lia)) as Hold.
  pose proof (karr_stage_quotient_minor previous pivot live selected (map f live)
    Hp Hlive_width Hlength Hpositive Hlive_quotient) as Hstage.
  cbn [length] in Hold. rewrite length_map in Hold.
  cbn [Nat.sub] in Hold. rewrite Nat.sub_0_r in Hold.
  cbn [map] in Hold.
  rewrite map_map in Hold. cbn [map nth] in Hold.
  replace (pivot_columns ++ head :: map (fun i => nth i columns 0%nat) selected)
    with ((pivot_columns ++ [head]) ++
      map (fun i => nth i columns 0%nat) selected) in Hold
    by (rewrite <- app_assoc; reflexivity).
  replace (pivot_rows ++ pivot_origin :: origins)
    with ((pivot_rows ++ [pivot_origin]) ++ origins) in Hold
    by (rewrite <- app_assoc; reflexivity).
  replace (length pivot_rows + S (length live))
    with (length (pivot_rows ++ [pivot_origin]) + length live) in Hold
    by (rewrite length_app; cbn [length]; lia).
  rewrite Hold in Hstage.
  assert (Hfactor : (previous ^ Z.of_nat (length live) <> 0)%Z).
  { apply Z.pow_nonzero; lia. }
  rewrite length_map. clear -Hstage Hfactor. nia.
Qed.

(** A selected concrete pivot preserves all-order minors on its reduced tails. *)
Lemma karr_minor_law_pivot_concrete : forall cols previous pivot_rows
    pivot_columns head columns labels rows pivot rest,
  length labels = length rows ->
  Forall (fun row => length (kcoeff row) = S cols) rows ->
  Forall (fun row => length (karr_row_entries row) = length (head :: columns)) rows ->
  karr_minor_law previous pivot_rows pivot_columns (head :: columns)
    (combine labels (map karr_row_entries rows)) ->
  previous <> 0%Z ->
  karr_pivot rows = Some (pivot, rest) ->
  exists origin remaining,
    Permutation labels (origin :: remaining) /\
    length remaining = length rest /\
    karr_head pivot =
      karr_determinant (S (length pivot_rows))
        (karr_submatrix (pivot_columns ++ [head])
          (pivot_rows ++ [origin])) /\
    karr_minor_law (karr_head pivot) (pivot_rows ++ [origin])
      (pivot_columns ++ [head]) columns
      (combine remaining
        (map karr_row_entries
          (map (fun row => karr_tail
            (karr_reduce previous (karr_head pivot) (karr_head row) pivot row))
            rest))).
Proof.
  intros cols previous pivot_rows pivot_columns head columns labels rows
    pivot rest Hlabels Hcoeff Hentries Hlaw Hprevious Hselect.
  destruct (karr_pivot_pairs_entries labels rows pivot rest Hlabels Hselect)
    as [origin [remaining [Hpair_perm [Hlabel_perm Hremaining]]]].
  exists origin, remaining. split; [exact Hlabel_perm|].
  split; [exact Hremaining|].
  pose proof (karr_pivot_some rows pivot rest Hselect) as [Ha Hrows_perm].
  pose proof (Permutation_Forall Hrows_perm Hcoeff) as Hcoeff_selected.
  pose proof (Permutation_Forall Hrows_perm Hentries) as Hentries_selected.
  apply Forall_cons_iff in Hcoeff_selected as [Hp_coeff Hrest_coeff].
  apply Forall_cons_iff in Hentries_selected as [Hp_entries Hrest_entries].
  assert (Hp_nonempty : kcoeff pivot <> []).
  { intro Hempty. rewrite Hempty in Hp_coeff. cbn [length] in Hp_coeff. lia. }
  assert (Ha_entries : karr_nth 0 (karr_row_entries pivot) = karr_head pivot)
    by (now apply karr_row_entries_head).
  set (pairs := (origin, karr_row_entries pivot) ::
    combine remaining (map karr_row_entries rest)).
  assert (Hlaw_selected : karr_minor_law previous pivot_rows pivot_columns
    (head :: columns) pairs).
  { eapply karr_minor_law_permutation; [exact Hpair_perm|exact Hlaw]. }
  split.
  - rewrite <- Ha_entries.
    eapply karr_minor_law_pivot_value; [exact Hlaw_selected|now left].
  - set (f := fun entries => karr_delete 0
    (map (fun z => (z / previous)%Z)
      (karr_cross (karr_head pivot) (karr_nth 0 entries)
        entries (karr_row_entries pivot)))).
  set (g := fun row => karr_tail
    (karr_reduce previous (karr_head pivot) (karr_head row) pivot row)).
  assert (Hactual : forall row, In row rest ->
    karr_row_entries (g row) = f (karr_row_entries row)).
  { intros row Hin.
    destruct (karr_pair_entries_origin remaining rest row Hremaining Hin)
      as [target Htarget].
    pose proof (proj1 (Forall_forall _ _) Hrest_coeff row Hin) as Hr_coeff.
    pose proof (proj1 (Forall_forall _ _) Hrest_entries row Hin) as Hr_entries.
    assert (Hweight : length (kweight row) = length (kweight pivot)).
    { apply karr_weight_width_of_entries;
        [rewrite Hr_coeff, Hp_coeff|rewrite Hr_entries, Hp_entries]; reflexivity. }
    assert (Hr_nonempty : kcoeff row <> []).
    { cbn beta in Hr_coeff. intro Hempty.
      rewrite Hempty in Hr_coeff. cbn [length] in Hr_coeff. lia. }
    assert (Hexact : karr_exact previous (KRow
      (karr_cross (karr_head pivot) (karr_head row)
        (kcoeff row) (kcoeff pivot))
      (karr_head pivot * kright row - karr_head row * kright pivot)%Z
      (karr_cross (karr_head pivot) (karr_head row)
        (kweight row) (kweight pivot))
      (karr_head pivot * kscale row - karr_head row * kscale pivot)%Z) = true).
    { eapply karr_minor_law_reduce_exact with (pivot_origin := origin)
        (target_origin := target) (pairs := pairs).
      - exact Hlaw_selected.
      - exact Hprevious.
      - now left.
      - now right.
      - cbn beta in Hr_coeff. lia.
      - lia.
      - exact Hp_nonempty.
      - exact Hr_nonempty.
      - exact Hp_entries.
      - cbn beta in Hr_entries. lia. }
    unfold g, f.
    rewrite (karr_reduced_tail_entries cols previous (karr_head pivot)
      (karr_head row) pivot row Hp_coeff Hr_coeff Hweight Hexact).
    now rewrite (karr_row_entries_head row Hr_nonempty). }
  assert (Hquotient : forall target entries,
    In (target, entries) (combine remaining (map karr_row_entries rest)) ->
    map (fun z => (previous * z)%Z) (f entries) =
      karr_delete 0
        (karr_cross (karr_nth 0 (karr_row_entries pivot))
          (karr_nth 0 entries) entries (karr_row_entries pivot))).
  { intros target entries Hin.
    destruct (karr_pair_entries_member remaining rest target entries Hin)
      as [row [Hrow Hrow_entries]]. subst entries.
    rewrite <- (Hactual row Hrow).
    pose proof (proj1 (Forall_forall _ _) Hrest_coeff row Hrow) as Hr_coeff.
    pose proof (proj1 (Forall_forall _ _) Hrest_entries row Hrow) as Hr_entries.
    eapply karr_minor_law_reduced_tail with (pivot_origin := origin)
      (target_origin := target) (pairs := pairs); eauto; try lia.
    - now left.
    - now right. }
  assert (Hwidth : forall target entries,
    In (target, entries) (combine remaining (map karr_row_entries rest)) ->
    length entries = length (karr_row_entries pivot)).
  { intros target entries Hin.
    destruct (karr_pair_entries_member remaining rest target entries Hin)
      as [row [Hrow Hrow_entries]]. subst entries.
    pose proof (proj1 (Forall_forall _ _) Hrest_entries row Hrow) as Hr_entries.
    cbn beta in Hr_entries. lia. }
  assert (Hminor : karr_minor_law (karr_nth 0 (karr_row_entries pivot))
    (pivot_rows ++ [origin]) (pivot_columns ++ [head]) columns
    (map (fun pair => (fst pair, f (snd pair)))
      (combine remaining (map karr_row_entries rest)))).
  { eapply karr_minor_law_pivot with (f := f).
    - exact Hlaw_selected.
    - exact Hprevious.
    - now rewrite Ha_entries.
    - exact Hwidth.
    - exact Hquotient. }
  rewrite Ha_entries in Hminor.
  rewrite <- (karr_pairs_map_rows remaining rest g f Hremaining Hactual) in Hminor.
  exact Hminor.
Qed.

(** A concrete nonzero pivot preserves the full labeled run invariant. *)
Lemma karr_run_state_pivot : forall width cols original previous pivot_rows
    pivot_columns head columns labels rows pivot rest,
  karr_run_state width (S cols) original previous pivot_rows pivot_columns
    (head :: columns) labels rows ->
  karr_pivot rows = Some (pivot, rest) ->
  exists origin remaining,
    karr_run_state width cols original (karr_head pivot)
      (pivot_rows ++ [origin]) (pivot_columns ++ [head]) columns remaining
      (map (fun row => karr_tail
        (karr_reduce previous (karr_head pivot) (karr_head row) pivot row))
        rest).
Proof.
  intros width cols original previous pivot_rows pivot_columns head columns
    labels rows pivot rest Hstate Hselect.
  unfold karr_run_state in Hstate. destruct Hstate as
    [Hprevious [Hdet [Hlabels [Hcoeff [Hentries [Hcolumns [Hsquare
      [Hpartition [Hincreasing [Hbounded Hlaw]]]]]]]]]].
  destruct (karr_minor_law_pivot_concrete cols previous pivot_rows
    pivot_columns head columns labels rows pivot rest Hlabels Hcoeff Hentries
    Hlaw Hprevious Hselect) as
    [origin [remaining [Hlabel_perm [Hremaining [Hnew_det Hminor]]]]].
  pose proof (karr_pivot_some rows pivot rest Hselect) as [Ha Hrows_perm].
  pose proof (Permutation_Forall Hrows_perm Hcoeff) as Hselected_coeff.
  pose proof (Permutation_Forall Hrows_perm Hentries) as Hselected_entries.
  apply Forall_cons_iff in Hselected_coeff as [Hp_coeff Hrest_coeff].
  apply Forall_cons_iff in Hselected_entries as [Hp_entries Hrest_entries].
  exists origin, remaining.
  unfold karr_run_state. repeat (apply conj).
  - exact Ha.
  - replace (length (pivot_rows ++ [origin])) with (S (length pivot_rows))
      by (rewrite length_app; cbn [length]; lia).
    exact Hnew_det.
  - now rewrite length_map.
  - apply Forall_forall. intros reduced Hin.
    apply in_map_iff in Hin as [row [Heq Hrow]]. subst reduced.
    pose proof (proj1 (Forall_forall _ _) Hrest_coeff row Hrow) as Hr_coeff.
    cbn beta in Hr_coeff.
    apply karr_tail_width.
    rewrite (karr_reduce_width previous (karr_head pivot) (karr_head row)
      pivot row ltac:(lia)). exact Hr_coeff.
  - apply Forall_forall. intros reduced Hin.
    apply in_map_iff in Hin as [row [Heq Hrow]]. subst reduced.
    pose proof (proj1 (Forall_forall _ _) Hrest_coeff row Hrow) as Hr_coeff.
    pose proof (proj1 (Forall_forall _ _) Hrest_entries row Hrow) as Hr_entries.
    cbn beta in Hr_coeff, Hr_entries.
    assert (Hweight : length (kweight row) = length (kweight pivot)).
    { apply karr_weight_width_of_entries;
        [rewrite Hr_coeff, Hp_coeff|rewrite Hr_entries, Hp_entries]; reflexivity. }
    assert (Hreduced_coeff : length (kcoeff
      (karr_reduce previous (karr_head pivot) (karr_head row) pivot row)) = S cols).
    { rewrite (karr_reduce_width previous (karr_head pivot) (karr_head row)
        pivot row ltac:(lia)). exact Hr_coeff. }
    assert (Hreduced_entries : length (karr_row_entries
      (karr_reduce previous (karr_head pivot) (karr_head row) pivot row)) =
      S (length columns)).
    { rewrite (karr_reduce_entries_width previous (karr_head pivot)
        (karr_head row) pivot row ltac:(lia) Hweight).
      rewrite Hr_entries. reflexivity. }
    rewrite karr_row_entries_tail.
    + destruct (karr_row_entries
        (karr_reduce previous (karr_head pivot) (karr_head row) pivot row))
        as [|z entries] eqn:Hshape;
        cbn [karr_delete length] in Hreduced_entries |- *; lia.
    + intro Hempty. rewrite Hempty in Hreduced_coeff.
      cbn [length] in Hreduced_coeff. lia.
  - cbn [length] in Hcolumns |- *. lia.
  - rewrite !length_app. cbn [length]. lia.
  - eapply Permutation_trans; [exact Hpartition|].
    replace ((pivot_rows ++ [origin]) ++ remaining) with
      (pivot_rows ++ origin :: remaining)
      by (rewrite <- app_assoc; reflexivity).
    now apply Permutation_app_head.
  - replace ((pivot_columns ++ [head]) ++ columns) with
      (pivot_columns ++ head :: columns)
      by (rewrite <- app_assoc; reflexivity).
    exact Hincreasing.
  - replace ((pivot_columns ++ [head]) ++ columns) with
      (pivot_columns ++ head :: columns)
      by (rewrite <- app_assoc; reflexivity).
    exact Hbounded.
  - exact Hminor.
Qed.

(** Projecting aligned row-entry pairs recovers their origin labels. *)
Lemma karr_pair_origins : forall (labels : list (list Z)) (rows : list karr_row),
  length labels = length rows ->
  map fst (combine labels (map karr_row_entries rows)) = labels.
Proof.
  intros labels. induction labels as [|label labels IH];
    intros [|row rows] Hlength; cbn [length] in Hlength;
    try discriminate; [reflexivity|].
  cbn [map combine fst]. f_equal. apply IH. lia.
Qed.

(** Every currently stored augmented entry is a signed source minor. *)
Lemma karr_run_state_entries : forall width cols original previous pivot_rows
    pivot_columns columns labels rows z,
  karr_run_state width cols original previous pivot_rows pivot_columns
    columns labels rows ->
  In z (flat_map karr_row_entries rows) ->
  In z (karr_signed_minors width original).
Proof.
  intros width cols original previous pivot_rows pivot_columns columns
    labels rows z Hstate Hin.
  unfold karr_run_state in Hstate. destruct Hstate as
    [_ [_ [Hlabels [_ [Hentries [_ [Hsquare [Hpartition
      [Hincreasing [Hbounded Hlaw]]]]]]]]]].
  apply in_flat_map in Hin as [row [Hrow Hz]].
  destruct (karr_pair_entries_origin labels rows row Hlabels Hrow)
    as [origin Hpair].
  rewrite <- (karr_pair_origins labels rows Hlabels) in Hpartition.
  eapply karr_minor_law_entry; eauto.
  exact (proj1 (Forall_forall _ _) Hentries row Hrow).
Qed.

(** Any uniform source-minor bit bound covers every current augmented row. *)
Lemma karr_run_state_bits : forall width cols original previous pivot_rows
    pivot_columns columns labels rows bits,
  karr_run_state width cols original previous pivot_rows pivot_columns
    columns labels rows ->
  (forall z, In z (karr_signed_minors width original) -> Z.size_nat z <= bits) ->
  Forall (fun row => Forall (fun z => Z.size_nat z <= bits)
    (karr_row_entries row)) rows.
Proof.
  intros width cols original previous pivot_rows pivot_columns columns labels
    rows bits Hstate Hbits.
  apply Forall_forall. intros row Hrow. apply Forall_forall. intros z Hz.
  apply Hbits. eapply karr_run_state_entries; [exact Hstate|].
  apply in_flat_map. now exists row.
Qed.

(** The current exact divisor is itself an enumerated pivot-prefix minor. *)
Lemma karr_run_state_previous_minor : forall width cols original previous
    pivot_rows pivot_columns columns labels rows,
  karr_run_state width cols original previous pivot_rows pivot_columns
    columns labels rows ->
  In previous (karr_signed_minors width original).
Proof.
  intros width cols original previous pivot_rows pivot_columns columns labels
    rows Hstate.
  unfold karr_run_state in Hstate. destruct Hstate as
    [_ [Hdet [_ [_ [_ [_ [Hsquare [Hpartition
      [Hincreasing [Hbounded _]]]]]]]]]].
  assert (Hinc : karr_increasing pivot_columns)
    by (eapply karr_increasing_prefix; exact Hincreasing).
  assert (Hbound : Forall (fun c => c < width) pivot_columns).
  { apply Forall_app in Hbounded as [Hprefix _]. exact Hprefix. }
  rewrite Hdet. destruct pivot_rows as [|row [|next rest]].
  - cbn [length karr_determinant]. apply karr_signed_minors_one.
  - destruct pivot_columns as [|column pivot_columns];
      [cbn [length] in Hsquare; lia|].
    destruct pivot_columns as [|second remaining];
      [|cbn [length] in Hsquare; lia].
    cbn [length] in Hsquare.
    cbn [length] in Hbound. apply Forall_cons_iff in Hbound as [Hcolumn _].
    cbn [app] in Hpartition.
    eapply karr_signed_minors_partition_one; [exact Hpartition|exact Hcolumn].
  - eapply karr_signed_minors_partition with (rest := labels).
    + cbn [length]. lia.
    + exact Hsquare.
    + exact Hpartition.
    + exact Hinc.
    + exact Hbound.
Qed.

(** A zero first entry of a live row is itself an enumerated source minor. *)
Lemma karr_run_state_zero_head : forall width cols original previous pivot_rows
    pivot_columns head columns labels rows row,
  karr_run_state width (S cols) original previous pivot_rows pivot_columns
    (head :: columns) labels rows ->
  In row rows -> karr_nth 0 (karr_row_entries row) = 0%Z ->
  In 0%Z (karr_signed_minors width original).
Proof.
  intros width cols original previous pivot_rows pivot_columns head columns
    labels rows row Hstate Hrow Hzero.
  assert (Hentries : length (karr_row_entries row) = S (length columns)).
  { unfold karr_run_state in Hstate.
    destruct Hstate as [_ [_ [_ [_ [Hwidth _]]]]].
    pose proof (proj1 (Forall_forall _ _) Hwidth row Hrow) as Hlength.
    cbn beta in Hlength. exact Hlength. }
  destruct (karr_row_entries row) as [|z entries] eqn:Hshape;
    cbn [length karr_nth] in Hentries, Hzero; [lia|].
  subst z. eapply karr_run_state_entries; [exact Hstate|].
  apply in_flat_map. exists row. split; [exact Hrow|].
  rewrite Hshape. now left.
Qed.

(** Failing a pivot on nonempty rows exposes a zero source minor. *)
Lemma karr_run_state_no_pivot_zero : forall width cols original previous
    pivot_rows pivot_columns head columns labels rows,
  karr_run_state width (S cols) original previous pivot_rows pivot_columns
    (head :: columns) labels rows ->
  rows <> [] -> karr_pivot rows = None ->
  In 0%Z (karr_signed_minors width original).
Proof.
  intros width cols original previous pivot_rows pivot_columns head columns
    labels [|row rows] Hstate Hnonempty Hnone; [contradiction|].
  pose proof (karr_pivot_none (row :: rows) Hnone) as Hheads.
  apply Forall_cons_iff in Hheads as [Hzero _].
  assert (Hcoeff : kcoeff row <> []).
  { unfold karr_run_state in Hstate.
    destruct Hstate as [_ [_ [_ [Hwidth _]]]].
    apply Forall_cons_iff in Hwidth as [Hrow _].
    intro Hempty. rewrite Hempty in Hrow. cbn [length] in Hrow. lia. }
  eapply karr_run_state_zero_head; [exact Hstate|now left|].
  now rewrite karr_row_entries_head.
Qed.

(** The concrete recorded run contains only source minors under the seed-zero condition. *)
Lemma karr_run_state_record : forall width original,
  (2 <= length original -> In 0%Z (karr_signed_minors width original)) ->
  forall cols previous pivot_rows pivot_columns columns labels rows z,
    karr_run_state width cols original previous pivot_rows pivot_columns
      columns labels rows ->
    In z (snd (karr_bareiss_record cols previous rows)) ->
    In z (karr_signed_minors width original).
Proof.
  intros width original Hzero_two cols. induction cols as [|cols IH];
    intros previous pivot_rows pivot_columns columns labels rows z Hstate Hin.
  - cbn [karr_bareiss_record snd] in Hin.
    eapply karr_run_state_entries; eauto.
  - destruct columns as [|head columns].
    { unfold karr_run_state in Hstate.
      destruct Hstate as [_ [_ [_ [_ [_ [Hcolumns _]]]]]].
      cbn [length] in Hcolumns. lia. }
    cbn [karr_bareiss_record] in Hin.
    destruct (karr_pivot rows) as [[pivot rest]|] eqn:Hselect.
    + set (g := fun row => karr_reduce previous (karr_head pivot)
        (karr_head row) pivot row).
      set (reduced := map g rest).
      change (map (fun row => karr_reduce previous (karr_head pivot)
        (karr_head row) pivot row) rest) with reduced in Hin.
      destruct (karr_bareiss_record cols (karr_head pivot)
        (map karr_tail reduced)) as [result history] eqn:Hrun.
      cbn [snd] in Hin.
      destruct (karr_run_state_pivot width cols original previous pivot_rows
        pivot_columns head columns labels rows pivot rest Hstate Hselect)
        as [origin [remaining Hnext]].
      assert (Hnext_rows : map karr_tail reduced =
        map (fun row => karr_tail (g row)) rest).
      { unfold reduced. now rewrite map_map. }
      unfold g in Hnext_rows. rewrite <- Hnext_rows in Hnext.
      assert (Hzero_rest : rest <> [] -> In 0%Z
        (karr_signed_minors width original)).
      { intro Hrest. apply Hzero_two.
        unfold karr_run_state in Hstate.
        destruct Hstate as [_ [_ [Hlabels [_ [_ [_ [_ [Hpartition _]]]]]]]].
        pose proof (Permutation_length Hpartition) as Horiginal.
        pose proof (Permutation_length
          (proj2 (karr_pivot_some rows pivot rest Hselect))) as Hrow_count.
        rewrite length_app in Horiginal. cbn [length] in Hrow_count.
        destruct rest as [|first rest]; [contradiction|].
        cbn [length] in Hrow_count. lia. }
      apply in_app_iff in Hin as [Hhere|Hother].
      * eapply karr_run_state_entries; [exact Hstate|exact Hhere].
      * apply in_app_iff in Hother as [Hraw|Hother].
        -- apply in_flat_map in Hraw as [reduced_row [Hreduced_row Hzrow]].
           apply in_map_iff in Hreduced_row as [source [Heq Hsource]].
           subst reduced_row.
           pose proof (proj2 (karr_pivot_some rows pivot rest Hselect))
             as Hrows_perm.
           unfold karr_run_state in Hstate.
           destruct Hstate as [_ [_ [_ [Hcoeff _]]]].
           pose proof (Permutation_Forall Hrows_perm Hcoeff) as Hselected.
           apply Forall_cons_iff in Hselected as [Hp_coeff Hrest_coeff].
           pose proof (proj1 (Forall_forall _ _) Hrest_coeff source Hsource)
             as Hsource_coeff.
           cbn beta in Hsource_coeff.
           assert (Hreduced_nonempty : kcoeff (g source) <> []).
           { unfold g. intro Hempty.
             pose proof (karr_reduce_width previous (karr_head pivot)
               (karr_head source) pivot source ltac:(lia)) as Hwidth.
             rewrite Hempty in Hwidth. cbn [length] in Hwidth. lia. }
           rewrite (karr_row_entries_zero_tail (g source)
             Hreduced_nonempty) in Hzrow
             by (unfold g; apply karr_reduce_head_zero).
           destruct Hzrow as [Hzero|Htail].
           ++ subst z. apply Hzero_rest.
              destruct rest; [contradiction|discriminate].
           ++ eapply karr_run_state_entries; [exact Hnext|].
              apply in_flat_map. exists (karr_tail (g source)). split.
              ** apply in_map_iff. exists (g source). split;
                   [reflexivity|apply in_map; exact Hsource].
              ** exact Htail.
        -- apply in_app_iff in Hother as [Hhistory|Houtput].
           ++ eapply IH; [exact Hnext|]. now rewrite Hrun.
           ++ apply in_flat_map in Houtput as [output [Houtput Hzrow]].
              cbn [List.In] in Houtput.
              destruct Houtput as [Hpivot|Hrestored].
              ** subst output.
                 eapply karr_run_state_entries; [exact Hstate|].
                 apply in_flat_map. exists pivot. split; [|exact Hzrow].
                 eapply Permutation_in;
                   [apply Permutation_sym, (proj2
                     (karr_pivot_some rows pivot rest Hselect))|now left].
              ** apply in_map_iff in Hrestored as [output' [Heq Hresult]].
                 subst output. rewrite karr_row_entries_restore in Hzrow.
                 destruct Hzrow as [Hzero|Htail].
                 --- subst z. apply Hzero_rest.
                     intro Hempty. subst rest. cbn [map] in Hrun.
                     rewrite karr_bareiss_record_empty in Hrun.
                     inversion Hrun; subst. contradiction.
                 --- apply IH with (previous := karr_head pivot)
                       (pivot_rows := pivot_rows ++ [origin])
                       (pivot_columns := pivot_columns ++ [head])
                       (columns := columns) (labels := remaining)
                       (rows := map karr_tail reduced);
                       [exact Hnext|].
                     rewrite Hrun.
                     eapply karr_bareiss_record_output; eauto.
                     apply in_flat_map. now exists output'.
    + destruct (karr_bareiss_record cols previous (map karr_tail rows))
        as [result history] eqn:Hrun.
      cbn [snd] in Hin.
      pose proof (karr_run_state_skip width cols original previous pivot_rows
        pivot_columns head columns labels rows Hstate) as Hnext.
      apply in_app_iff in Hin as [Hhere|Hother].
      * eapply karr_run_state_entries; [exact Hstate|exact Hhere].
      * apply in_app_iff in Hother as [Hhistory|Houtput].
        -- eapply IH; [exact Hnext|]. now rewrite Hrun.
        -- apply in_flat_map in Houtput as [output [Houtput Hzrow]].
           apply in_map_iff in Houtput as [source [Heq Hsource]].
           subst output. rewrite karr_row_entries_restore in Hzrow.
           destruct Hzrow as [Hzero|Htail].
           ++ subst z. eapply karr_run_state_no_pivot_zero;
                [exact Hstate| |exact Hselect].
              intro Hempty. subst rows. cbn [map] in Hrun.
              rewrite karr_bareiss_record_empty in Hrun.
              inversion Hrun; subst. contradiction.
           ++ eapply IH; [exact Hnext|]. rewrite Hrun.
              eapply karr_bareiss_record_output; eauto.
              apply in_flat_map. now exists source.
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

(** The recorded run returns rows with the input coefficient width. *)
Lemma karr_bareiss_record_width : forall cols previous rows,
  Forall (fun r => length (kcoeff r) = cols) rows ->
  Forall (fun r => length (kcoeff r) = cols)
    (fst (karr_bareiss_record cols previous rows)).
Proof.
  intros cols previous rows Hwidth.
  rewrite karr_bareiss_record_value.
  apply karr_echelon_width, karr_bareiss_echelon. exact Hwidth.
Qed.

(** Bareiss elimination preserves each multiplier-vector width. *)
Lemma karr_bareiss_weight_width : forall cols previous rows mlen,
  Forall (fun r => length (kcoeff r) = cols) rows ->
  Forall (fun r => length (kweight r) = mlen) rows ->
  Forall (fun r => length (kweight r) = mlen)
    (karr_bareiss cols previous rows).
Proof.
  intro cols. induction cols as [|cols IH];
    intros previous rows mlen Hcoeff Hweight; [exact Hweight|].
  cbn [karr_bareiss]. destruct (karr_pivot rows) as [[pivot rest]|] eqn:Hselect.
  - destruct (karr_pivot_some _ _ _ Hselect) as [_ Hperm].
    pose proof (Permutation_Forall Hperm Hcoeff) as Hselected_coeff.
    pose proof (Permutation_Forall Hperm Hweight) as Hselected_weight.
    apply Forall_cons_iff in Hselected_coeff as [Hpcoeff Hrestcoeff].
    apply Forall_cons_iff in Hselected_weight as [Hpweight Hrestweight].
    constructor; [exact Hpweight|]. apply Forall_map.
    apply IH.
    + apply Forall_map, Forall_forall. intros r Hr.
      pose proof (proj1 (Forall_forall _ _) Hrestcoeff r Hr) as Hrcoeff.
      apply karr_tail_width.
      rewrite karr_reduce_width; [exact Hrcoeff|].
      cbn beta in Hrcoeff. lia.
    + apply Forall_map, Forall_forall. intros r Hr.
      pose proof (proj1 (Forall_forall _ _) Hrestcoeff r Hr) as Hrcoeff.
      pose proof (proj1 (Forall_forall _ _) Hrestweight r Hr) as Hrweight.
      cbn beta in Hrcoeff, Hrweight.
      assert (Hsame_coeff : length (kcoeff r) = length (kcoeff pivot)) by lia.
      assert (Hsame_weight : length (kweight r) = length (kweight pivot)) by lia.
      pose proof (karr_weight_width_of_entries
        (karr_reduce previous (karr_head pivot) (karr_head r) pivot r) r
        (karr_reduce_width previous (karr_head pivot) (karr_head r)
          pivot r Hsame_coeff)
        (karr_reduce_entries_width previous (karr_head pivot) (karr_head r)
          pivot r Hsame_coeff Hsame_weight)) as Hreduced.
      cbn [karr_tail kweight]. lia.
  - apply Forall_map. apply IH.
    + apply Forall_map, Forall_forall. intros r Hr.
      pose proof (proj1 (Forall_forall _ _) Hcoeff r Hr) as Hrcoeff.
      now apply karr_tail_width.
    + apply Forall_map, Forall_forall. intros r Hr.
      cbn [karr_tail kweight].
      exact (proj1 (Forall_forall _ _) Hweight r Hr).
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

(** One coordinate of a finite integer combination of dense rows. *)
Definition karr_weighted_entry (rows : list karr_row) (weights : list Z) (i : nat) : Z :=
  fold_right Z.add 0%Z
    (map (fun rm => (snd rm * karr_nth i (kcoeff (fst rm)))%Z)
      (List.combine rows weights)).

(** A coordinate zero in every source row is zero in every weighted combination. *)
Lemma karr_weighted_entry_zero : forall rows weights i,
  Forall (fun r => karr_nth i (kcoeff r) = 0%Z) rows ->
  karr_weighted_entry rows weights i = 0%Z.
Proof.
  intros rows weights i Hzero. revert weights.
  induction Hzero as [|r rows Hhead Htail IH]; intros [|m weights]; try reflexivity.
  change ((m * karr_nth i (kcoeff r) + karr_weighted_entry rows weights i)%Z = 0%Z).
  rewrite Hhead, IH. lia.
Qed.

(** Later rows have zero coefficients at every preceding row's pivot. *)
Lemma karr_ordered_later_zero : forall p rows i a,
  karr_ordered (p :: rows) ->
  Forall (fun r => exists j b, karr_first (kcoeff r) = Some (j, b)) rows ->
  karr_first (kcoeff p) = Some (i, a) ->
  Forall (fun r => karr_nth i (kcoeff r) = 0%Z) rows.
Proof.
  intros p rows i a Hordered Hnonzero Hfirst.
  inversion Hordered as [|p' rows' Htail Hbefore]; subst p' rows'.
  apply Forall_forall. intros r Hr.
  destruct (proj1 (Forall_forall _ _) Hnonzero r Hr) as [j [b Hrfirst]].
  apply karr_first_before with (i := j) (a := b); [exact Hrfirst|].
  now apply Hbefore with (a := a) (q := r) (b := b).
Qed.

(** Ordered rows with nonzero pivots admit only the trivial zero combination. *)
Lemma karr_ordered_zero_weights : forall rows weights,
  karr_ordered rows ->
  Forall (fun r => exists i a, karr_first (kcoeff r) = Some (i, a)) rows ->
  length weights = length rows ->
  (forall i, karr_weighted_entry rows weights i = 0%Z) ->
  Forall (fun m => m = 0%Z) weights.
Proof.
  intros rows weights Hordered. revert weights.
  induction Hordered as [|p rows Hordered IH Hbefore];
    intros [|m weights] Hnonzero Hlength Hzero;
    cbn [length] in Hlength; try discriminate; [constructor|].
  inversion Hnonzero as [|p' rows' Hp Htail]; subst p' rows'.
  destruct Hp as [i [a Hfirst]].
  assert (Hlater : Forall (fun r => karr_nth i (kcoeff r) = 0%Z) rows).
  { apply karr_ordered_later_zero with (p := p) (a := a); [now constructor| |];
      assumption. }
  pose proof (Hzero i) as Hcoordinate.
  change ((m * karr_nth i (kcoeff p) + karr_weighted_entry rows weights i)%Z = 0%Z)
    in Hcoordinate.
  rewrite (karr_first_nth _ _ _ Hfirst),
    (karr_weighted_entry_zero rows weights i Hlater) in Hcoordinate.
  assert (Hproduct : (m * a)%Z = 0%Z) by lia.
  apply Z.mul_eq_0 in Hproduct as [Hm|Ha].
  - subst m. constructor; [reflexivity|]. apply IH; [exact Htail|lia|].
    intro j. pose proof (Hzero j) as Hj.
    change (karr_weighted_entry rows weights j = 0%Z) in Hj. exact Hj.
  - exfalso. exact (karr_first_nonzero _ _ _ Hfirst Ha).
Qed.

(** Filtering rows preserves their strict pivot order. *)
Lemma karr_ordered_filter : forall test rows,
  karr_ordered rows -> karr_ordered (filter test rows).
Proof.
  intros test rows Hordered.
  induction Hordered as [|p rows Hordered IH Hbefore]; cbn [filter]; [constructor|].
  destruct (test p); [constructor|exact IH]; [exact IH|].
  intros i a q j b Hp Hq Hfirst. apply filter_In in Hq as [Hq _].
  now apply Hbefore with (a := a) (q := q) (b := b).
Qed.

(** A coefficient list with no first nonzero entry consists entirely of zeros. *)
Lemma karr_first_none_zero : forall zs,
  karr_first zs = None -> forallb (Z.eqb 0) zs = true.
Proof.
  intro zs. induction zs as [|z zs IH]; intro Hnone; [reflexivity|].
  cbn [karr_first] in Hnone. destruct (Z.eqb z 0) eqn:Hzero; [|discriminate].
  apply Z.eqb_eq in Hzero. subst z.
  destruct (karr_first zs) as [[i a]|] eqn:Hfirst; [discriminate|].
  change (forallb (Z.eqb 0) zs = true). now apply IH.
Qed.

(** Every nonzero dense row has an actual first pivot. *)
Lemma karr_nonzero_has_first : forall r, karr_zero r = false ->
  exists i a, karr_first (kcoeff r) = Some (i, a).
Proof.
  intros r Hnonzero. destruct (karr_first (kcoeff r)) as [[i a]|] eqn:Hfirst.
  - exists i, a. reflexivity.
  - unfold karr_zero in Hnonzero.
    rewrite (karr_first_none_zero _ Hfirst) in Hnonzero. discriminate.
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

  (** Scaling visits each stored occurrence exactly once. *)
  Definition scale_coef (a : Z) (xs : list (X.t * Z)) : list (X.t * Z) :=
    map (fun p => (fst p, (a * snd p)%Z)) xs.

  (** Substitution scales the affine form once by the complete replaced coefficient. *)
  Definition subst (x : X.t) (f : lin X.t) (r : lcons X.t) : lcons X.t :=
    let a := coefficient x (lhs r) in
    normalize_row (LCons _
      (filter (fun p => negb (X.eqb (fst p) x)) (lhs r) ++
        scale_coef a (coef f))
      (lrel r) (rhs r - a * cst f)%Z).

  Definition mentions (x : X.t) (r : lcons X.t) : bool :=
    negb (Z.eqb (coefficient x (lhs r)) 0).

  Definition projected_row (x : X.t) (xs : list X.t) (P : list (lcons X.t))
      (r : karr_row) : option (lcons X.t) :=
    let c := LCons _ (sparse xs (kcoeff r)) REq (kright r) in
    if negb (mentions x c) && C.check_entails P c (Cert (kweight r) 1 false)
    then Some c else None.

  (** Projection shares one normalized source across seeding, checking and retention. *)
  Definition project (x : X.t) (P : list (lcons X.t)) : list (lcons X.t) :=
    let Pn := map normalize_row P in
    let xs := x :: filter (fun y => negb (X.eqb y x)) (variables P) in
    let rows := karr_bareiss 1 1 (seed_rows xs (length P) 0 Pn) in
    present (map (projected_row x xs Pn) rows) ++
      filter (fun r => match lrel r with
        | REq => false | RLe => negb (mentions x r) end) Pn.


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

  (** Affine range production and checking share the same prepared source rows. *)
  Definition range_linear (P : list (lcons X.t)) (f : lin X.t) : bnd * bnd :=
    let prepared := map normalize_row P in
    let xs := variables (LCons _ (coef f) REq 0 :: prepared) in
    let r := karr_target (equality_basis xs prepared) 1
      (KRow (map (fun x => coefficient x (coef f)) xs) 0
        (repeat 0%Z (length prepared)) 1) in
    let z := (- kright r / kscale r + cst f)%Z in
    match entail_cert prepared (LCons _ (coef f) REq (z - cst f)%Z) with
    | Some _ => (Fin z, Fin z)
    | None => (NegInf, PosInf)
    end.

  Definition range (e : term L.op X.t) (s : t) : bnd * bnd :=
    match s, F.lin_of e with
    | Reached P, Some (f, NoWrap) => range_linear P f
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

  (** A source and its coefficient-normalized form have exactly the same models. *)
  Lemma normalize_rows_sat : forall P v,
    Forall (sat v) (map normalize_row P) <-> Forall (sat v) P.
  Proof.
    intros P v. rewrite Forall_map. split; intro Hmodels;
      apply Forall_forall; intros r Hin; apply normalize_row_sat;
      exact (proj1 (Forall_forall _ _) Hmodels r Hin).
  Qed.

  (** Projection keeps every state obtained by assigning an arbitrary new value. *)
  Lemma project_sound : forall x P v z, Forall (sat v) P ->
    Forall (sat (upd X.eqb v x z)) (project x P).
  Proof.
    intros x P v z Hmodels.
    assert (Hnormalized : Forall (sat v) (map normalize_row P)).
    { now apply normalize_rows_sat. }
    unfold project. apply Forall_app. split.
    - apply present_forall. intros r c Hrow.
      eapply projected_row_sound; [exact Hrow | exact Hnormalized].
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
  (** A successful hull extractor returns its sparse equality row unchanged. *)
  Lemma checked_hull_row_shape : forall xs a b r c,
    checked_hull_row xs a b r = Some c ->
    c = LCons X.t (sparse xs (skipn (S (length xs)) (kcoeff r))) REq
      (karr_nth (length xs) (skipn (S (length xs)) (kcoeff r))).
  Proof.
    intros xs a b r c Hrow. unfold checked_hull_row in Hrow.
    remember (LCons X.t (sparse xs (skipn (S (length xs)) (kcoeff r))) REq
      (karr_nth (length xs) (skipn (S (length xs)) (kcoeff r)))) as candidate
      eqn:Hcandidate in Hrow.
    destruct (forallb (Z.eqb 0) (firstn (S (length xs)) (kcoeff r)) &&
      negb (forallb (Z.eqb 0) (skipn (S (length xs)) (kcoeff r))) &&
      C.check_entails a candidate (Cert (firstn (length a) (kweight r)) 1 false) &&
      C.check_entails b candidate (Cert (skipn (length a) (kweight r)) 1 false));
      [|discriminate].
    injection Hrow as Hsame. subst c. exact Hcandidate.
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
  Proof.
    intros a b P Hjoin. change (Reached (affine_hull a b) = Reached P) in Hjoin.
    injection Hjoin as Hsame. subst P. unfold affine_hull. apply present_forall.
    intros r c Hrow. rewrite (checked_hull_row_shape _ _ _ _ _ Hrow). reflexivity.
  Qed.

  Lemma wrank_rows : forall p P, wrank p (Reached P) = length P.
  Proof.
    intros p P. reflexivity.
  Qed.
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

  (** Splitting a full equality multiplier vector preserves both source predicates. *)
  Lemma hull_weights_split : forall A B ms,
    equality_weights (A ++ B) ms ->
    equality_weights A (firstn (length A) ms) /\
      equality_weights B (skipn (length A) ms).
  Proof.
    intro A. induction A as [|p A IH]; intros B [|m ms] Hweights.
    - split; [constructor|exact Hweights].
    - split; [constructor|exact Hweights].
    - inversion Hweights.
    - inversion Hweights as [|p' m' rows weights Hhead Htail]; subst p' m' rows weights.
      destruct (IH B ms Htail) as [HA HB]. cbn [length firstn skipn].
      split; [now constructor|exact HB].
  Qed.

  (** Concatenating source equality multipliers preserves the whole predicate. *)
  Lemma hull_weights_app : forall A B ms ns,
    equality_weights A ms -> equality_weights B ns ->
    equality_weights (A ++ B) (ms ++ ns).
  Proof.
    intros A B ms ns HA HB. induction HA as [|p m A ms Hhead Htail IH];
      cbn [app]; [exact HB|now constructor].
  Qed.

  (** Prefix splitting commutes with scaling a multiplier vector. *)
  Lemma hull_firstn_scale : forall n a zs,
    firstn n (map (fun z => (a * z)%Z) zs) =
      map (fun z => (a * z)%Z) (firstn n zs).
  Proof.
    intro n. induction n as [|n IH]; intros a [|z zs]; cbn; try reflexivity.
    now rewrite IH.
  Qed.

  (** Suffix splitting commutes with scaling a multiplier vector. *)
  Lemma hull_skipn_scale : forall n a zs,
    skipn n (map (fun z => (a * z)%Z) zs) =
      map (fun z => (a * z)%Z) (skipn n zs).
  Proof.
    intro n. induction n as [|n IH]; intros a [|z zs]; cbn; try reflexivity.
    apply IH.
  Qed.

  (** Prefix splitting commutes with crossing two multiplier vectors. *)
  Lemma hull_firstn_cross : forall n a b xs ys,
    firstn n (karr_cross a b xs ys) =
      karr_cross a b (firstn n xs) (firstn n ys).
  Proof.
    intro n. induction n as [|n IH]; intros a b [|x xs] [|y ys];
      cbn [firstn karr_cross]; try reflexivity. now rewrite IH.
  Qed.

  (** Suffix splitting commutes with crossing two multiplier vectors. *)
  Lemma hull_skipn_cross : forall n a b xs ys,
    skipn n (karr_cross a b xs ys) =
      karr_cross a b (skipn n xs) (skipn n ys).
  Proof.
    intro n. induction n as [|n IH]; intros a b [|x xs] [|y ys];
      cbn [skipn karr_cross]; try reflexivity.
    - destruct (skipn n xs); reflexivity.
    - apply IH.
  Qed.

  (** Crossing vectors preserves equally sized block boundaries. *)
  Lemma hull_cross_app : forall xs ys us vs a b,
    length xs = length ys ->
    karr_cross a b (xs ++ us) (ys ++ vs) =
      karr_cross a b xs ys ++ karr_cross a b us vs.
  Proof.
    intro xs. induction xs as [|x xs IH]; intros [|y ys] us vs a b Hlength;
      cbn [length] in Hlength; try discriminate.
    - reflexivity.
    - cbn [app karr_cross]. now rewrite IH by lia.
  Qed.

  (** The lifted vector records the difference block and the right source equation. *)
  Definition hull_coordinates (xs : list X.t) (A B : list (lcons X.t)) (ms : list Z)
      : list Z :=
    let left := firstn (length A) ms in
    let right := skipn (length A) ms in
    (map (fun x => (C.comb_coef A left x - C.comb_coef B right x)%Z) xs ++
      [(- C.comb_rhs A left + C.comb_rhs B right)%Z]) ++
    (map (fun x => C.comb_coef B right x) xs ++ [C.comb_rhs B right]).

  (** Eliminated columns remain zero while the full lifted provenance is retained. *)
  Definition hull_tracks (A B : list (lcons X.t)) (xs : list X.t)
      (offset : nat) (r : karr_row) : Prop :=
    equality_weights (A ++ B) (kweight r) /\
      repeat 0%Z offset ++ kcoeff r = hull_coordinates xs A B (kweight r).

  (** A lifted vector scales by the same integer as its tracked multipliers. *)
  Lemma hull_coordinates_scale : forall xs A B ms a,
    map (fun z => (a * z)%Z) (hull_coordinates xs A B ms) =
      hull_coordinates xs A B (map (fun z => (a * z)%Z) ms).
  Proof.
    intros xs A B ms a. unfold hull_coordinates.
    rewrite hull_firstn_scale, hull_skipn_scale, !map_app, !map_map.
    cbn [map]. rewrite !comb_rhs_scale.
    apply f_equal2.
    - apply f_equal2.
      + apply map_ext. intro x. rewrite !comb_coef_scale. ring.
      + f_equal. ring.
    - apply f_equal2.
      + apply map_ext. intro x. rewrite comb_coef_scale. ring.
      + reflexivity.
  Qed.

  (** Crossing tracked multipliers crosses each block of the lifted vectors. *)
  Lemma hull_coordinates_cross : forall xs A B ms ns a b,
    equality_weights (A ++ B) ms -> equality_weights (A ++ B) ns ->
    karr_cross a b (hull_coordinates xs A B ms) (hull_coordinates xs A B ns) =
      hull_coordinates xs A B (karr_cross a b ms ns).
  Proof.
    intros xs A B ms ns a b Hms Hns.
    destruct (hull_weights_split A B ms Hms) as [Hma Hmb].
    destruct (hull_weights_split A B ns Hns) as [Hna Hnb].
    assert (Hleft : length (firstn (length A) ms) = length (firstn (length A) ns)).
    { rewrite <- (equality_weights_length _ _ Hma),
        <- (equality_weights_length _ _ Hna). reflexivity. }
    assert (Hright : length (skipn (length A) ms) = length (skipn (length A) ns)).
    { rewrite <- (equality_weights_length _ _ Hmb),
        <- (equality_weights_length _ _ Hnb). reflexivity. }
    unfold hull_coordinates. rewrite hull_firstn_cross, hull_skipn_cross.
    rewrite hull_cross_app by now rewrite !length_app, !length_map.
    rewrite !hull_cross_app by now rewrite !length_map.
    rewrite !cross_coordinate_map. cbn [karr_cross].
    rewrite !(comb_rhs_cross A _ _ a b Hleft), !(comb_rhs_cross B _ _ a b Hright).
    apply f_equal2.
    - apply f_equal2.
      + apply map_ext. intro x.
        rewrite (comb_coef_cross A _ _ a b x Hleft),
          (comb_coef_cross B _ _ a b x Hright). ring.
      + f_equal. ring.
    - apply f_equal2.
      + apply map_ext. intro x. now rewrite (comb_coef_cross B _ _ a b x Hright).
      + reflexivity.
  Qed.

  (** Cancelling a common nonzero factor preserves full lifted provenance. *)
  Lemma hull_tracks_factor : forall A B xs offset factor r s,
    factor <> 0%Z -> karr_multiple factor r s -> hull_tracks A B xs offset s ->
    hull_tracks A B xs offset r.
  Proof.
    intros A B xs offset factor r s Hnonzero [Hcoeff [_ [Hweight _]]] [Hweights Hcoords].
    split.
    - apply equality_weights_factor with (factor := factor); [exact Hnonzero|].
      now rewrite Hweight.
    - apply scale_list_injective with (factor := factor); [exact Hnonzero|].
      rewrite scale_zero_prefix, Hcoeff, Hcoords, hull_coordinates_scale, Hweight.
      reflexivity.
  Qed.

  (** Guarded division preserves full lifted provenance in either executable branch. *)
  Lemma hull_tracks_divide : forall A B xs offset divisor r,
    hull_tracks A B xs offset r -> hull_tracks A B xs offset (karr_divide divisor r).
  Proof.
    intros A B xs offset divisor r Htracks.
    destruct (karr_divide_factor divisor r) as [factor [Hnonzero Hmultiple]].
    now apply hull_tracks_factor with (factor := factor) (s := r).
  Qed.

  (** Every fraction-free row reduction preserves the two exact source combinations. *)
  Lemma hull_tracks_reduce : forall A B xs offset divisor a b p r,
    hull_tracks A B xs offset p -> hull_tracks A B xs offset r ->
    hull_tracks A B xs offset (karr_reduce divisor a b p r).
  Proof.
    intros A B xs offset divisor a b p r [Hpw Hpc] [Hrw Hrc].
    unfold karr_reduce. apply hull_tracks_divide. split.
    - cbn [kweight]. now apply equality_weights_cross.
    - cbn [kcoeff kweight]. rewrite <- cross_zero_prefix, Hrc, Hpc.
      now apply hull_coordinates_cross.
  Qed.

  (** The full lifted row always has two blocks of one more than the source dimension. *)
  Lemma hull_tracks_width : forall A B xs offset r,
    hull_tracks A B xs offset r -> offset + length (kcoeff r) = 2 * length xs + 2.
  Proof.
    intros A B xs offset r [_ Hcoords].
    pose proof (f_equal (@length Z) Hcoords) as Hlength.
    unfold hull_coordinates in Hlength.
    rewrite !length_app, repeat_length, !length_map in Hlength. cbn [length] in Hlength.
    lia.
  Qed.

  (** Dropping a zero leading column advances the restored-column offset. *)
  Lemma hull_tracks_tail : forall A B xs offset r,
    hull_tracks A B xs offset r -> offset < 2 * length xs + 2 -> karr_head r = 0%Z ->
    hull_tracks A B xs (S offset) (karr_tail r).
  Proof.
    intros A B xs offset r Htracks Hroom Hzero.
    pose proof (hull_tracks_width _ _ _ _ _ Htracks) as Hwidth.
    destruct Htracks as [Hweights Hcoords].
    destruct (kcoeff r) as [|a zs] eqn:Hcoeff; [cbn [length] in Hwidth; lia|].
    unfold karr_head in Hzero. rewrite Hcoeff in Hzero. subst a.
    split; [exact Hweights|]. cbn [karr_tail kcoeff kweight].
    rewrite Hcoeff. cbn [tl]. rewrite zero_prefix_succ. exact Hcoords.
  Qed.

  (** Restoring a zero leading column returns to the preceding offset. *)
  Lemma hull_tracks_restore : forall A B xs offset r,
    hull_tracks A B xs (S offset) r -> hull_tracks A B xs offset (karr_restore r).
  Proof.
    intros A B xs offset r [Hweights Hcoords]. split; [exact Hweights|].
    cbn [karr_restore kcoeff kweight]. now rewrite <- zero_prefix_succ.
  Qed.

  (** Restoring a whole triangular suffix preserves each tracked row. *)
  Lemma hull_tracks_restore_map : forall A B xs offset rs,
    Forall (hull_tracks A B xs (S offset)) rs ->
    Forall (hull_tracks A B xs offset) (map karr_restore rs).
  Proof.
    intros A B xs offset rs Htracks. apply Forall_forall. intros r Hin.
    apply in_map_iff in Hin as [s [Hsame Hin]]. subst r. apply hull_tracks_restore.
    now apply (proj1 (Forall_forall _ _) Htracks).
  Qed.

  (** Bareiss elimination preserves both exact input combinations through every column. *)
  Lemma hull_bareiss_tracks : forall cols A B xs offset previous rs,
    offset + cols <= 2 * length xs + 2 -> Forall (hull_tracks A B xs offset) rs ->
    Forall (hull_tracks A B xs offset) (karr_bareiss cols previous rs).
  Proof.
    intro cols. induction cols as [|cols IH];
      intros A B xs offset previous rs Hroom Hrows; [exact Hrows|].
    cbn [karr_bareiss]. destruct (karr_pivot rs) as [[p rest]|] eqn:Hpivot.
    - destruct (karr_pivot_some _ _ _ Hpivot) as [_ Hperm].
      assert (Hordered : Forall (hull_tracks A B xs offset) (p :: rest)).
      { eapply Permutation_Forall; [exact Hperm|exact Hrows]. }
      inversion Hordered as [|p' rest' Hp Hrest]; subst p' rest'.
      constructor; [exact Hp|]. apply hull_tracks_restore_map. apply IH; [lia|].
      apply Forall_forall. intros r Hin.
      apply in_map_iff in Hin as [s [Hsame Hin]]. subst r.
      apply hull_tracks_tail; [|lia|apply karr_reduce_head_zero].
      apply hull_tracks_reduce; [exact Hp|].
      now apply (proj1 (Forall_forall _ _) Hrest).
    - apply hull_tracks_restore_map. apply IH; [lia|].
      pose proof (karr_pivot_none _ Hpivot) as Hheads.
      apply Forall_forall. intros r Hin.
      apply in_map_iff in Hin as [s [Hsame Hin]]. subst r.
      apply hull_tracks_tail; [|lia|].
      + now apply (proj1 (Forall_forall _ _) Hrows).
      + now apply (proj1 (Forall_forall _ _) Hheads).
  Qed.

  (** Repeated zeros split across any two consecutive lengths. *)
  Lemma hull_repeat_app : forall n m,
    repeat 0%Z (n + m) = repeat 0%Z n ++ repeat 0%Z m.
  Proof.
    intro n. induction n as [|n IH]; intro m; cbn; [reflexivity|now rewrite IH].
  Qed.

  (** Every identity multiplier row has the declared number of entries. *)
  Lemma hull_unit_length : forall n i, length (karr_unit n i) = n.
  Proof.
    intro n. induction n as [|n IH]; intros [|i]; cbn [karr_unit length];
      try reflexivity; [now rewrite repeat_length|now rewrite IH].
  Qed.

  (** A left-source unit vector has zero entries throughout the right-source suffix. *)
  Lemma hull_unit_left : forall n m i, i < n ->
    karr_unit (n + m) i = karr_unit n i ++ repeat 0%Z m.
  Proof.
    intro n. induction n as [|n IH]; intros m i Hbound; [lia|].
    destruct i as [|i]; cbn [Nat.add karr_unit app].
    - f_equal. apply hull_repeat_app.
    - f_equal. apply IH. lia.
  Qed.

  (** A right-source unit vector has a zero left-source prefix. *)
  Lemma hull_unit_right : forall n m i,
    karr_unit (n + m) (n + i) = repeat 0%Z n ++ karr_unit m i.
  Proof.
    intro n. induction n as [|n IH]; intros m i;
      cbn [Nat.add karr_unit repeat app]; [reflexivity|now rewrite IH].
  Qed.

  (** A split at a list's exact length recovers its two appended blocks. *)
  Lemma hull_split_app : forall n (ms ns : list Z), length ms = n ->
    firstn n (ms ++ ns) = ms /\ skipn n (ms ++ ns) = ns.
  Proof.
    intros n ms. revert n. induction ms as [|m ms IH]; intros n ns Hlength.
    - cbn [length] in Hlength. subst n. split; reflexivity.
    - destruct n as [|n]; [discriminate|].
      cbn [length] in Hlength. destruct (IH n ns ltac:(lia)) as [Hfirst Hskip].
      cbn [firstn skipn app]. split; [now rewrite Hfirst|exact Hskip].
  Qed.

  (** Zero multipliers give zero source coefficients. *)
  Lemma hull_comb_coef_zero : forall P x,
    C.comb_coef P (repeat 0%Z (length P)) x = 0%Z.
  Proof.
    intros P x. change (row_sum P (repeat 0%Z (length P))
      (fun r => C.coef_of x (lhs r)) = 0%Z). apply row_sum_zero.
  Qed.

  (** Zero multipliers give a zero source right-hand side. *)
  Lemma hull_comb_rhs_zero : forall P,
    C.comb_rhs P (repeat 0%Z (length P)) = 0%Z.
  Proof.
    intro P. change (row_sum P (repeat 0%Z (length P)) rhs = 0%Z).
    apply row_sum_zero.
  Qed.

  (** Mapping every coordinate to zero gives a zero block of the same length. *)
  Lemma hull_map_zero : forall (xs : list X.t),
    map (fun _ => 0%Z) xs = repeat 0%Z (length xs).
  Proof.
    intro xs. induction xs as [|x xs IH]; cbn; [reflexivity|now rewrite IH].
  Qed.

  (** Appending one zero extends a zero block by one entry. *)
  Lemma hull_zero_snoc : forall n,
    repeat 0%Z n ++ [0%Z] = repeat 0%Z (S n).
  Proof.
    intro n. induction n as [|n IH]; cbn; [reflexivity|now rewrite IH].
  Qed.

  (** A left unit vector reconstructs precisely its lifted source row. *)
  Lemma hull_coordinates_left_unit : forall xs A B i p,
    nth_error A i = Some p ->
    hull_coordinates xs A B (karr_unit (length A + length B) i) =
      dense xs p ++ (- rhs p)%Z :: repeat 0%Z (S (length xs)).
  Proof.
    intros xs A B i p Hnth.
    assert (Hbound : i < length A).
    { apply nth_error_Some. rewrite Hnth. discriminate. }
    unfold hull_coordinates. rewrite (hull_unit_left _ _ _ Hbound).
    destruct (hull_split_app (length A) (karr_unit (length A) i)
      (repeat 0%Z (length B)) (hull_unit_length _ _)) as [Hfirst Hskip].
    rewrite Hfirst, Hskip, (comb_rhs_unit A i p Hnth), hull_comb_rhs_zero.
    assert (Hleft : map (fun x =>
      (C.comb_coef A (karr_unit (length A) i) x -
       C.comb_coef B (repeat 0%Z (length B)) x)%Z) xs = dense xs p).
    { unfold dense. apply map_ext. intro x.
      rewrite (comb_coef_unit A i p x Hnth), hull_comb_coef_zero. ring. }
    assert (Hright : map (fun x => C.comb_coef B (repeat 0%Z (length B)) x) xs =
      repeat 0%Z (length xs)).
    { rewrite <- hull_map_zero. apply map_ext. intro x. apply hull_comb_coef_zero. }
    rewrite Hleft, Hright, Z.add_0_r, hull_zero_snoc. now rewrite <- app_assoc.
  Qed.

  (** A right unit vector reconstructs precisely its lifted source row. *)
  Lemma hull_coordinates_right_unit : forall xs A B i p,
    nth_error B i = Some p ->
    hull_coordinates xs A B (karr_unit (length A + length B) (length A + i)) =
      map Z.opp (dense xs p) ++ rhs p :: dense xs p ++ [rhs p].
  Proof.
    intros xs A B i p Hnth. unfold hull_coordinates. rewrite hull_unit_right.
    destruct (hull_split_app (length A) (repeat 0%Z (length A))
      (karr_unit (length B) i) ltac:(apply repeat_length)) as [Hfirst Hskip].
    rewrite Hfirst, Hskip, hull_comb_rhs_zero, (comb_rhs_unit B i p Hnth).
    assert (Hleft : map (fun x =>
      (C.comb_coef A (repeat 0%Z (length A)) x -
       C.comb_coef B (karr_unit (length B) i) x)%Z) xs = map Z.opp (dense xs p)).
    { unfold dense. rewrite map_map. apply map_ext. intro x.
      rewrite hull_comb_coef_zero, (comb_coef_unit B i p x Hnth). ring. }
    assert (Hright : map (fun x => C.comb_coef B (karr_unit (length B) i) x) xs =
      dense xs p).
    { unfold dense. apply map_ext. intro x. now apply comb_coef_unit with (index := i). }
    rewrite Hleft, Hright. cbn [Z.opp Z.add]. now rewrite <- app_assoc.
  Qed.

  (** A left seed carries the original source index through skipped inequalities. *)
  Lemma hull_left_member : forall xs total rows index r,
    In r (hull_left xs total index rows) ->
    exists i p, nth_error rows i = Some p /\ lrel p = REq /\
      r = KRow (dense xs p ++ (- rhs p)%Z :: repeat 0%Z (S (length xs)))
        0 (karr_unit total (index + i)) 0.
  Proof.
    intros xs total rows. induction rows as [|p rows IH]; intros index r Hin;
      [contradiction|].
    cbn [hull_left] in Hin. destruct (lrel p) eqn:Hrel.
    - cbn [In] in Hin. destruct Hin as [Hsame|Hin].
      + subst r. exists 0, p. split; [reflexivity|]. split; [exact Hrel|].
        now rewrite Nat.add_0_r.
      + destruct (IH _ _ Hin) as [i [q [Hnth [Heq Hrow]]]].
        exists (S i), q. split; [exact Hnth|]. split; [exact Heq|].
        replace (index + S i) with (S index + i) by lia. exact Hrow.
    - destruct (IH _ _ Hin) as [i [q [Hnth [Heq Hrow]]]].
      exists (S i), q. split; [exact Hnth|]. split; [exact Heq|].
      replace (index + S i) with (S index + i) by lia. exact Hrow.
  Qed.

  (** A right seed carries the original source index through skipped inequalities. *)
  Lemma hull_right_member : forall xs total rows index r,
    In r (hull_right xs total index rows) ->
    exists i p, nth_error rows i = Some p /\ lrel p = REq /\
      r = KRow (map Z.opp (dense xs p) ++ rhs p :: dense xs p ++ [rhs p])
        0 (karr_unit total (index + i)) 0.
  Proof.
    intros xs total rows. induction rows as [|p rows IH]; intros index r Hin;
      [contradiction|].
    cbn [hull_right] in Hin. destruct (lrel p) eqn:Hrel.
    - cbn [In] in Hin. destruct Hin as [Hsame|Hin].
      + subst r. exists 0, p. split; [reflexivity|]. split; [exact Hrel|].
        now rewrite Nat.add_0_r.
      + destruct (IH _ _ Hin) as [i [q [Hnth [Heq Hrow]]]].
        exists (S i), q. split; [exact Hnth|]. split; [exact Heq|].
        replace (index + S i) with (S index + i) by lia. exact Hrow.
    - destruct (IH _ _ Hin) as [i [q [Hnth [Heq Hrow]]]].
      exists (S i), q. split; [exact Hnth|]. split; [exact Heq|].
      replace (index + S i) with (S index + i) by lia. exact Hrow.
  Qed.

  (** Every normalized left seed retains its exact raw-source provenance. *)
  Lemma hull_left_tracks : forall xs A B,
    Forall (hull_tracks A B xs 0)
      (hull_left xs (length A + length B) 0 (map normalize_row A)).
  Proof.
    intros xs A B. apply Forall_forall. intros r Hin.
    destruct (hull_left_member _ _ _ _ _ Hin) as [i [p [Hnth [Hrel Hrow]]]].
    rewrite nth_error_map in Hnth.
    destruct (nth_error A i) as [q|] eqn:Hq; [|discriminate].
    injection Hnth as Hsame. subst p. subst r. cbn [Nat.add] in *.
    assert (Hbound : i < length A).
    { apply nth_error_Some. rewrite Hq. discriminate. }
    split.
    - cbn [kweight]. rewrite (hull_unit_left _ _ _ Hbound). apply hull_weights_app.
      + now apply equality_weights_unit with (p := q).
      + apply equality_weights_zero.
    - cbn [repeat app kcoeff kweight]. rewrite dense_normalize_row.
      cbn [normalize_row rhs].
      symmetry. apply hull_coordinates_left_unit. exact Hq.
  Qed.

  (** Every normalized right seed retains its exact raw-source provenance. *)
  Lemma hull_right_tracks : forall xs A B,
    Forall (hull_tracks A B xs 0)
      (hull_right xs (length A + length B) (length A) (map normalize_row B)).
  Proof.
    intros xs A B. apply Forall_forall. intros r Hin.
    destruct (hull_right_member _ _ _ _ _ Hin) as [i [p [Hnth [Hrel Hrow]]]].
    rewrite nth_error_map in Hnth.
    destruct (nth_error B i) as [q|] eqn:Hq; [|discriminate].
    injection Hnth as Hsame. subst p. subst r. split.
    - cbn [kweight]. rewrite hull_unit_right. apply hull_weights_app.
      + apply equality_weights_zero.
      + now apply equality_weights_unit with (p := q).
    - cbn [repeat app kcoeff kweight]. rewrite dense_normalize_row.
      cbn [normalize_row rhs].
      symmetry. apply hull_coordinates_right_unit. exact Hq.
  Qed.

  (** The actual lifted basis retains exact combinations of both raw input states. *)
  Lemma hull_basis_tracks : forall xs A B,
    Forall (hull_tracks A B xs 0)
      (karr_bareiss (2 * length xs + 2) 1
        (hull_left xs (length A + length B) 0 (map normalize_row A) ++
         hull_right xs (length A + length B) (length A) (map normalize_row B))).
  Proof.
    intros xs A B. apply hull_bareiss_tracks; [lia|]. apply Forall_app. split.
    - apply hull_left_tracks.
    - apply hull_right_tracks.
  Qed.

  (** Splitting after the auxiliary columns exposes the two blocks of lifted provenance. *)
  Lemma hull_coordinates_parts : forall xs A B ms,
    firstn (S (length xs)) (hull_coordinates xs A B ms) =
      map (fun x => (C.comb_coef A (firstn (length A) ms) x -
        C.comb_coef B (skipn (length A) ms) x)%Z) xs ++
        [(- C.comb_rhs A (firstn (length A) ms) +
          C.comb_rhs B (skipn (length A) ms))%Z] /\
    skipn (S (length xs)) (hull_coordinates xs A B ms) =
      map (fun x => C.comb_coef B (skipn (length A) ms) x) xs ++
        [C.comb_rhs B (skipn (length A) ms)].
  Proof.
    intros xs A B ms. unfold hull_coordinates. apply hull_split_app.
    rewrite length_app, length_map. cbn [length]. lia.
  Qed.

  (** Pairing coordinates with their values ignores every trailing constant coordinate. *)
  Lemma hull_combine_extra : forall (xs : list X.t) (f : X.t -> Z) zs,
    List.combine xs (map f xs ++ zs) = map (fun x => (x, f x)) xs.
  Proof.
    intro xs. induction xs as [|x xs IH]; intros f zs; cbn; [reflexivity|].
    now rewrite IH.
  Qed.

  (** The coordinate immediately after all variable coefficients is the recorded constant. *)
  Lemma hull_nth_extra : forall (xs : list X.t) (f : X.t -> Z) b,
    karr_nth (length xs) (map f xs ++ [b]) = b.
  Proof.
    intro xs. induction xs as [|x xs IH]; intros f b;
      cbn [length map app karr_nth]; [reflexivity|apply IH].
  Qed.

  (** Sparse extraction recovers a coefficient function supported by the coordinate list. *)
  Lemma hull_sparse_coefficient : forall xs f b x,
    NoDup xs -> (forall y, ~ In y xs -> f y = 0%Z) ->
    coefficient x (sparse xs (map f xs ++ [b])) = f x.
  Proof.
    intros xs f b x Hunique Hsupport. unfold sparse.
    rewrite coefficient_nonzero, hull_combine_extra.
    assert (Hdec : {In x xs} + {~ In x xs}).
    { apply in_dec. intros y z. destruct (X.eqb_spec y z); auto. }
    destruct Hdec as [Hin|Habsent].
    - now apply coefficient_coordinates.
    - rewrite Hsupport by exact Habsent. apply coefficient_absent.
      rewrite map_map. change (~ In x (map (fun y => y) xs)). now rewrite map_id.
  Qed.

  (** A missing normalized key has total coefficient zero in the original raw row. *)
  Lemma hull_source_coefficient_zero : forall rows xs r x,
    (forall s, In s rows -> forall y z, In (y, z) (lhs (normalize_row s)) -> In y xs) ->
    In r rows -> ~ In x xs -> coefficient x (lhs r) = 0%Z.
  Proof.
    intros rows xs r x Hsupport Hr Habsent.
    rewrite <- normalize_coef_coefficient. apply coefficient_absent.
    intro Hin. apply in_map_iff in Hin as [[y z] [Hsame Hin]]. cbn [fst] in Hsame.
    subst y. apply Habsent. now apply Hsupport with (s := r) (z := z).
  Qed.

  (** Returning a hull row requires every auxiliary coefficient to be zero. *)
  Lemma checked_hull_row_aux_zero : forall xs A B r c,
    checked_hull_row xs A B r = Some c ->
    forallb (Z.eqb 0) (firstn (S (length xs)) (kcoeff r)) = true.
  Proof.
    intros xs A B r c Hrow. unfold checked_hull_row in Hrow.
    remember (LCons X.t (sparse xs (skipn (S (length xs)) (kcoeff r))) REq
      (karr_nth (length xs) (skipn (S (length xs)) (kcoeff r)))) as candidate
      eqn:Hcandidate in Hrow.
    destruct (forallb (Z.eqb 0) (firstn (S (length xs)) (kcoeff r)) &&
      negb (forallb (Z.eqb 0) (skipn (S (length xs)) (kcoeff r))) &&
      C.check_entails A candidate (Cert (firstn (length A) (kweight r)) 1 false) &&
      C.check_entails B candidate (Cert (skipn (length A) (kweight r)) 1 false))
      eqn:Hcheck; [|discriminate].
    apply andb_true_iff in Hcheck as [Hcheck _].
    apply andb_true_iff in Hcheck as [Hcheck _].
    now apply andb_true_iff in Hcheck as [Hcheck _].
  Qed.

  (** Zero auxiliary columns turn exact lifted provenance into two scale-one certificates. *)
  Lemma checked_hull_row_certificates : forall xs A B r c,
    NoDup xs ->
    (forall s, In s (A ++ B) -> forall x z,
      In (x, z) (lhs (normalize_row s)) -> In x xs) ->
    hull_tracks A B xs 0 r -> checked_hull_row xs A B r = Some c ->
    equality_certificate A c (firstn (length A) (kweight r)) 1 /\
      equality_certificate B c (skipn (length A) (kweight r)) 1.
  Proof.
    intros xs A B r c Hunique Hsupport [Hweights Hcoords] Hrow.
    cbn [repeat app] in Hcoords.
    set (ma := firstn (length A) (kweight r)).
    set (mb := skipn (length A) (kweight r)).
    destruct (hull_weights_split A B (kweight r) Hweights) as [Hma Hmb].
    fold ma mb in Hma, Hmb.
    destruct (hull_coordinates_parts xs A B (kweight r)) as [Hprefix Hsuffix].
    fold ma mb in Hprefix, Hsuffix.
    pose proof (checked_hull_row_aux_zero _ _ _ _ _ Hrow) as Hzero.
    rewrite Hcoords, Hprefix, forallb_app in Hzero.
    apply andb_true_iff in Hzero as [Hzero Hright].
    cbn [forallb] in Hright. apply andb_true_iff in Hright as [Hright _].
    apply Z.eqb_eq in Hright.
    assert (Houtside : forall x, ~ In x xs ->
      C.comb_coef A ma x = 0%Z /\ C.comb_coef B mb x = 0%Z).
    { intros x Habsent. split; apply comb_coef_zero; intros s Hs.
      - apply hull_source_coefficient_zero with (rows := A ++ B) (xs := xs);
          [exact Hsupport|apply in_or_app; now left|exact Habsent].
      - apply hull_source_coefficient_zero with (rows := A ++ B) (xs := xs);
          [exact Hsupport|apply in_or_app; now right|exact Habsent]. }
    assert (Hsame : forall x, C.comb_coef A ma x = C.comb_coef B mb x).
    { intro x. assert (Hdec : {In x xs} + {~ In x xs}).
      { apply in_dec. intros y z. destruct (X.eqb_spec y z); auto. }
      destruct Hdec as [Hin|Habsent].
      - assert (Hentry : Z.eqb 0 (C.comb_coef A ma x - C.comb_coef B mb x) = true).
        { apply (proj1 (forallb_forall _ _) Hzero).
          apply in_map_iff. exists x. split; [reflexivity|exact Hin]. }
        apply Z.eqb_eq in Hentry. lia.
      - destruct (Houtside x Habsent) as [HA HB]. now rewrite HA, HB. }
    pose proof (checked_hull_row_shape _ _ _ _ _ Hrow) as Hshape.
    rewrite Hcoords, Hsuffix, hull_nth_extra in Hshape.
    assert (Hcoefficient : forall x, C.coef_of x (lhs c) = C.comb_coef B mb x).
    { intro x. rewrite Hshape. change (coefficient x
        (sparse xs (map (fun y => C.comb_coef B mb y) xs ++ [C.comb_rhs B mb])) =
        C.comb_coef B mb x).
      apply hull_sparse_coefficient; [exact Hunique|].
      intros y Habsent. exact (proj2 (Houtside y Habsent)). }
    assert (Hrelation : lrel c = REq) by now rewrite Hshape.
    assert (Hrhs : rhs c = C.comb_rhs B mb) by now rewrite Hshape.
    unfold equality_certificate. split.
    - split; [exact Hma|]. split; [lia|]. split.
      + intro x. rewrite Hcoefficient, Hsame. ring.
      + rewrite Hrelation, Hrhs. lia.
    - split; [exact Hmb|]. split; [lia|]. split.
      + intro x. rewrite Hcoefficient. ring.
      + rewrite Hrelation, Hrhs. ring.
  Qed.

  (** Every emitted hull row belongs to both exact input spans, even for infeasible sources. *)
  Lemma affine_hull_span : forall A B,
    Forall (in_span A) (affine_hull A B) /\ Forall (in_span B) (affine_hull A B).
  Proof.
    intros A B. set (xs := variables (map normalize_row A ++ map normalize_row B)).
    assert (Hunique : NoDup xs) by apply variables_nodup.
    assert (Hsupport : forall s, In s (A ++ B) -> forall x z,
      In (x, z) (lhs (normalize_row s)) -> In x xs).
    { intros s Hs x z Hterm. unfold xs.
      apply variables_contains with (r := normalize_row s) (z := z); [|exact Hterm].
      rewrite <- map_app. now apply in_map. }
    assert (Hboth : Forall (fun c => in_span A c /\ in_span B c) (affine_hull A B)).
    { unfold affine_hull. fold xs. apply present_forall_in. intros r Hr c Hrow.
      pose proof (proj1 (Forall_forall _ _) (hull_basis_tracks xs A B) r Hr) as Htracks.
      destruct (checked_hull_row_certificates xs A B r c Hunique Hsupport Htracks Hrow)
        as [HA HB]. split.
      - now apply span_of_certificate with (ms := firstn (length A) (kweight r)) (sc := 1%Z).
      - now apply span_of_certificate with (ms := skipn (length A) (kweight r)) (sc := 1%Z). }
    split; apply Forall_forall; intros c Hc.
    - exact (proj1 (proj1 (Forall_forall _ _) Hboth c Hc)).
    - exact (proj2 (proj1 (Forall_forall _ _) Hboth c Hc)).
  Qed.


  (** Join rows have exact combination witnesses from both input states. *)
  Lemma join_span : forall a b P, join (Reached a) (Reached b) = Reached P ->
    Forall (in_span a) P /\ Forall (in_span b) P.
  Proof.
    intros A B P Hjoin. change (Reached (affine_hull A B) = Reached P) in Hjoin.
    injection Hjoin as Hsame. subst P. apply affine_hull_span.
  Qed.

  (** A list recognized as all zero is its explicit zero block. *)
  Lemma hull_zero_list : forall zs, forallb (Z.eqb 0) zs = true ->
    zs = repeat 0%Z (length zs).
  Proof.
    intro zs. induction zs as [|z zs IH]; intro Hzero; [reflexivity|].
    cbn [forallb] in Hzero. apply andb_true_iff in Hzero as [Hz Htail].
    apply Z.eqb_eq in Hz. subst z. cbn [length repeat]. f_equal. exact (IH Htail).
  Qed.

  (** Suffixes of an all-zero list are also all zero. *)
  Lemma hull_zero_skipn : forall n zs, forallb (Z.eqb 0) zs = true ->
    forallb (Z.eqb 0) (skipn n zs) = true.
  Proof.
    intro n. induction n as [|n IH]; intros zs Hzero; [exact Hzero|].
    destruct zs as [|z zs]; [reflexivity|].
    cbn [forallb] in Hzero. apply andb_true_iff in Hzero as [_ Htail].
    cbn [skipn]. now apply IH.
  Qed.

  (** A returned hull row has a nonzero output block. *)
  Lemma checked_hull_row_suffix_nonzero : forall xs A B r c,
    checked_hull_row xs A B r = Some c ->
    forallb (Z.eqb 0) (skipn (S (length xs)) (kcoeff r)) = false.
  Proof.
    intros xs A B r c Hrow. unfold checked_hull_row in Hrow.
    remember (LCons X.t (sparse xs (skipn (S (length xs)) (kcoeff r))) REq
      (karr_nth (length xs) (skipn (S (length xs)) (kcoeff r)))) as candidate
      eqn:Hcandidate in Hrow.
    destruct (forallb (Z.eqb 0) (firstn (S (length xs)) (kcoeff r)) &&
      negb (forallb (Z.eqb 0) (skipn (S (length xs)) (kcoeff r))) &&
      C.check_entails A candidate (Cert (firstn (length A) (kweight r)) 1 false) &&
      C.check_entails B candidate (Cert (skipn (length A) (kweight r)) 1 false))
      eqn:Hcheck; [|discriminate].
    apply andb_true_iff in Hcheck as [Hcheck _].
    apply andb_true_iff in Hcheck as [Hcheck _].
    apply andb_true_iff in Hcheck as [_ Hcheck]. now apply negb_true_iff.
  Qed.

  (** Every returned hull row comes from a dense row with an actual nonzero pivot. *)
  Lemma checked_hull_row_first : forall xs A B r c,
    checked_hull_row xs A B r = Some c ->
    exists i a, karr_first (kcoeff r) = Some (i, a).
  Proof.
    intros xs A B r c Hrow. apply karr_nonzero_has_first.
    unfold karr_zero. destruct (forallb (Z.eqb 0) (kcoeff r)) eqn:Hzero; [|reflexivity].
    pose proof (hull_zero_skipn (S (length xs)) _ Hzero) as Hsuffix.
    rewrite (checked_hull_row_suffix_nonzero _ _ _ _ _ Hrow) in Hsuffix. discriminate.
  Qed.

  (** Sparse extraction faithfully reconstructs the complete nonzero lifted row. *)
  Lemma checked_hull_row_embedding : forall xs A B r c,
    NoDup xs ->
    (forall s, In s (A ++ B) -> forall x z,
      In (x, z) (lhs (normalize_row s)) -> In x xs) ->
    hull_tracks A B xs 0 r -> checked_hull_row xs A B r = Some c ->
    kcoeff r = repeat 0%Z (S (length xs)) ++ (dense xs c ++ [rhs c]).
  Proof.
    intros xs A B r c Hunique Hsupport Htracks Hrow.
    destruct (checked_hull_row_certificates xs A B r c Hunique Hsupport Htracks Hrow)
      as [_ [Hweights [Hpositive [Hcoefficient Hrhs]]]].
    pose proof (checked_hull_row_shape _ _ _ _ _ Hrow) as Hshape.
    assert (Hrelation : lrel c = REq) by now rewrite Hshape.
    rewrite Hrelation in Hrhs.
    destruct Htracks as [_ Hcoords]. cbn [repeat app] in Hcoords.
    destruct (hull_coordinates_parts xs A B (kweight r)) as [Hprefix Hsuffix].
    pose proof (checked_hull_row_aux_zero _ _ _ _ _ Hrow) as Hzero.
    rewrite Hcoords, Hprefix in Hzero. apply hull_zero_list in Hzero.
    rewrite length_app, length_map in Hzero. cbn [length] in Hzero.
    replace (length xs + 1) with (S (length xs)) in Hzero by lia.
    rewrite Hcoords. unfold hull_coordinates. rewrite Hzero. apply f_equal.
    apply f_equal2.
    - unfold dense. apply map_ext. intro x. specialize (Hcoefficient x).
      change (C.comb_coef B (skipn (length A) (kweight r)) x =
        (1 * coefficient x (lhs c))%Z) in Hcoefficient. lia.
    - f_equal. lia.
  Qed.

  (** Retained dense rows are the successful positions of an optional row emitter. *)
  Definition hull_kept (emit : karr_row -> option (lcons X.t)) (rows : list karr_row)
      : list karr_row :=
    filter (fun r => match emit r with Some _ => true | None => false end) rows.

  (** Output observations align position by position with the retained dense rows. *)
  Lemma hull_emit_observations : forall emit entry rows,
    (forall r, In r rows -> forall c, emit r = Some c ->
      forall i, karr_nth i (kcoeff r) = entry c i) ->
    Forall2 (fun r c => forall i, karr_nth i (kcoeff r) = entry c i)
      (hull_kept emit rows) (present (map emit rows)).
  Proof.
    intros emit entry rows. induction rows as [|r rows IH]; intro Hobserve; [constructor|].
    cbn [hull_kept filter map present flat_map]. destruct (emit r) as [c|] eqn:Hrow.
    - constructor.
      + exact (Hobserve r (or_introl eq_refl) c Hrow).
      + apply IH. intros s Hs d Hd i. exact (Hobserve s (or_intror Hs) d Hd i).
    - apply IH. intros s Hs d Hd i. exact (Hobserve s (or_intror Hs) d Hd i).
  Qed.

  (** Retained positions have pivots whenever every successful emitted row does. *)
  Lemma hull_emit_firsts : forall emit rows,
    (forall r, In r rows -> forall c, emit r = Some c ->
      exists i a, karr_first (kcoeff r) = Some (i, a)) ->
    Forall (fun r => exists i a, karr_first (kcoeff r) = Some (i, a)) (hull_kept emit rows).
  Proof.
    intros emit rows Hfirst. apply Forall_forall. intros r Hr.
    unfold hull_kept in Hr. apply filter_In in Hr as [Hr Hkeep].
    destruct (emit r) as [c|] eqn:Hrow; [|discriminate].
    now apply Hfirst with (c := c).
  Qed.

  (** Aligned emitted observations have equally many dense and sparse rows. *)
  Lemma hull_observations_length : forall (entry : lcons X.t -> nat -> Z) rows cs,
    Forall2 (fun r c => forall i, karr_nth i (kcoeff r) = entry c i) rows cs ->
    length rows = length cs.
  Proof.
    intros entry rows cs Hobserve. induction Hobserve; cbn; congruence.
  Qed.

  (** Weighted sums commute with positionwise dense-to-sparse observations. *)
  Lemma hull_weighted_observations : forall entry rows cs,
    Forall2 (fun r c => forall i, karr_nth i (kcoeff r) = entry c i) rows cs ->
    forall weights i, karr_weighted_entry rows weights i =
      row_sum cs weights (fun c => entry c i).
  Proof.
    intros entry rows cs Hobserve.
    induction Hobserve as [|r c rows cs Hhead Htail IH]; intros [|m weights] i;
      try reflexivity.
    change ((m * karr_nth i (kcoeff r) + karr_weighted_entry rows weights i)%Z =
      (m * entry c i + row_sum cs weights (fun c => entry c i))%Z).
    now rewrite Hhead, IH.
  Qed.

  (** Optional extraction preserves independence whenever it preserves all dense coordinates. *)
  Lemma hull_ordered_output_weights : forall emit entry rows weights,
    karr_ordered rows ->
    (forall r, In r rows -> forall c, emit r = Some c ->
      (exists i a, karr_first (kcoeff r) = Some (i, a)) /\
      (forall i, karr_nth i (kcoeff r) = entry c i)) ->
    length weights = length (present (map emit rows)) ->
    (forall i, row_sum (present (map emit rows)) weights (fun c => entry c i) = 0%Z) ->
    Forall (fun m => m = 0%Z) weights.
  Proof.
    intros emit entry rows weights Hordered Hemit Hlength Hzero.
    assert (Hobserve : Forall2
      (fun r c => forall i, karr_nth i (kcoeff r) = entry c i)
      (hull_kept emit rows) (present (map emit rows))).
    { apply hull_emit_observations. intros r Hr c Hc. exact (proj2 (Hemit r Hr c Hc)). }
    apply karr_ordered_zero_weights with (rows := hull_kept emit rows).
    - unfold hull_kept. now apply karr_ordered_filter.
    - apply hull_emit_firsts. intros r Hr c Hc. exact (proj1 (Hemit r Hr c Hc)).
    - rewrite (hull_observations_length _ _ _ Hobserve). exact Hlength.
    - intro i. rewrite (hull_weighted_observations _ _ _ Hobserve). apply Hzero.
  Qed.

  (** A weighted sum is zero when every source contributes zero to its entry. *)
  Lemma hull_row_sum_entries_zero : forall rows weights entry,
    Forall (fun r => entry r = 0%Z) rows -> row_sum rows weights entry = 0%Z.
  Proof.
    intros rows weights entry Hzero. revert weights.
    induction Hzero as [|r rows Hhead Htail IH]; intros [|m weights]; try reflexivity.
    change ((m * entry r + row_sum rows weights entry)%Z = 0%Z).
    rewrite Hhead, IH. ring.
  Qed.

  (** Zero coefficient and RHS combinations give zero at every augmented coordinate. *)
  Lemma hull_sum_dense_zero : forall xs rows weights,
    (forall x, C.comb_coef rows weights x = 0%Z) -> C.comb_rhs rows weights = 0%Z ->
    forall i, row_sum rows weights
      (fun r => karr_nth i (dense xs r ++ [rhs r])) = 0%Z.
  Proof.
    intro xs. induction xs as [|x xs IH]; intros rows weights Hcoef Hrhs [|i].
    - change (C.comb_rhs rows weights = 0%Z). exact Hrhs.
    - apply hull_row_sum_entries_zero. apply Forall_forall. intros r _.
      destruct i; reflexivity.
    - change (C.comb_coef rows weights x = 0%Z). apply Hcoef.
    - change (row_sum rows weights
        (fun r => karr_nth i (dense xs r ++ [rhs r])) = 0%Z).
      now apply IH.
  Qed.

  (** Adding a zero prefix preserves zero weighted sums at every coordinate. *)
  Lemma hull_sum_prefix_zero : forall n xs rows weights,
    (forall x, C.comb_coef rows weights x = 0%Z) -> C.comb_rhs rows weights = 0%Z ->
    forall i, row_sum rows weights
      (fun r => karr_nth i (repeat 0%Z n ++ (dense xs r ++ [rhs r]))) = 0%Z.
  Proof.
    intro n. induction n as [|n IH]; intros xs rows weights Hcoef Hrhs i.
    - now apply hull_sum_dense_zero.
    - destruct i as [|i].
      + apply hull_row_sum_entries_zero. apply Forall_forall. intros r _. reflexivity.
      + change (row_sum rows weights
          (fun r => karr_nth i (repeat 0%Z n ++ (dense xs r ++ [rhs r]))) = 0%Z).
        now apply IH.
  Qed.

  (** One output row is observed in the complete lifted coordinate system. *)
  Definition hull_output_entry (xs : list X.t) (r : lcons X.t) (i : nat) : Z :=
    karr_nth i (repeat 0%Z (S (length xs)) ++ (dense xs r ++ [rhs r])).

  (** Every zero integer combination of affine-hull output rows has only zero multipliers. *)
  Lemma hull_affine_zero_weights : forall A B weights,
    length weights = length (affine_hull A B) ->
    (forall x, C.comb_coef (affine_hull A B) weights x = 0%Z) ->
    C.comb_rhs (affine_hull A B) weights = 0%Z ->
    Forall (fun m => m = 0%Z) weights.
  Proof.
    intros A B weights Hlength Hcoef Hrhs.
    set (xs := variables (map normalize_row A ++ map normalize_row B)).
    set (rows := karr_bareiss (2 * length xs + 2) 1
      (hull_left xs (length A + length B) 0 (map normalize_row A) ++
       hull_right xs (length A + length B) (length A) (map normalize_row B))).
    assert (Hunique : NoDup xs) by apply variables_nodup.
    assert (Hsupport : forall s, In s (A ++ B) -> forall x z,
      In (x, z) (lhs (normalize_row s)) -> In x xs).
    { intros s Hs x z Hterm. unfold xs.
      apply variables_contains with (r := normalize_row s) (z := z); [|exact Hterm].
      rewrite <- map_app. now apply in_map. }
    assert (Hordered : karr_ordered rows).
    { unfold rows. apply karr_echelon_ordered with (n := 2 * length xs + 2).
      apply karr_bareiss_echelon. apply hull_seed_width. }
    apply hull_ordered_output_weights with (emit := checked_hull_row xs A B)
      (entry := hull_output_entry xs) (rows := rows).
    - exact Hordered.
    - intros r Hr c Hrow. split.
      + now apply checked_hull_row_first with (xs := xs) (A := A) (B := B) (c := c).
      + intro i. rewrite (checked_hull_row_embedding xs A B r c Hunique Hsupport).
        * reflexivity.
        * exact (proj1 (Forall_forall _ _) (hull_basis_tracks xs A B) r Hr).
        * exact Hrow.
    - exact Hlength.
    - intro i. change (row_sum (affine_hull A B) weights
        (fun c => hull_output_entry xs c i) = 0%Z).
      unfold hull_output_entry. now apply hull_sum_prefix_zero.
  Qed.

  (** Removing an existing list position decreases length by exactly one. *)
  Lemma hull_others_length : forall (P : list (lcons X.t)) i r, nth_error P i = Some r ->
    S (length (firstn i P ++ skipn (S i) P)) = length P /\
      i <= length (firstn i P ++ skipn (S i) P).
  Proof.
    intro P. induction P as [|p P IH]; intros [|i] r Hnth;
      cbn [nth_error] in Hnth; try discriminate.
    - cbn [firstn skipn app length]. split; lia.
    - destruct (IH i r Hnth) as [Hlength Hbound].
      change (S (S (length (firstn i P ++ skipn (S i) P))) = S (length P) /\
        S i <= S (length (firstn i P ++ skipn (S i) P))). split; lia.
  Qed.

  (** Inserting a multiplier at an existing prefix boundary increases its length by one. *)
  Lemma hull_insert_length : forall i (weights : list Z) m, i <= length weights ->
    length (firstn i weights ++ m :: skipn i weights) = S (length weights).
  Proof.
    intro i. induction i as [|i IH]; intros [|w weights] m Hbound;
      cbn [firstn skipn app length] in *; try reflexivity; try lia.
    now rewrite IH by lia.
  Qed.

  (** Inserting one multiplier separates its contribution from all remaining positions. *)
  Lemma hull_insert_sum : forall P i r weights m entry,
    nth_error P i = Some r -> i <= length weights ->
    row_sum P (firstn i weights ++ m :: skipn i weights) entry =
      (m * entry r + row_sum (firstn i P ++ skipn (S i) P) weights entry)%Z.
  Proof.
    intro P. induction P as [|p P IH]; intros [|i] r weights m entry Hnth Hbound;
      cbn [nth_error] in Hnth; try discriminate.
    - injection Hnth as Hsame. subst r. reflexivity.
    - destruct weights as [|w weights]; [cbn [length] in Hbound; lia|].
      cbn [length] in Hbound.
      change ((w * entry p + row_sum P
        (firstn i weights ++ m :: skipn i weights) entry)%Z =
        (m * entry r + (w * entry p +
          row_sum (firstn i P ++ skipn (S i) P) weights entry))%Z).
      rewrite (IH i r weights m entry Hnth ltac:(lia)). ring.
  Qed.


  (** Every emitted equality is independent of all other emitted rows. *)
  Lemma join_independent : forall a b P, join (Reached a) (Reached b) = Reached P ->
    forall i r, nth_error P i = Some r -> ~ in_span (firstn i P ++ skipn (S i) P) r.
  Proof.
    intros A B P Hjoin i r Hnth Hspan.
    change (Reached (affine_hull A B) = Reached P) in Hjoin.
    injection Hjoin as Hsame. subst P.
    assert (Hrelation : lrel r = REq).
    { pose proof (join_eq A B (affine_hull A B) eq_refl) as Hrelations.
      apply (proj1 (Forall_forall _ _) Hrelations). now apply nth_error_In with (n := i). }
    destruct (span_equality_certificate _ r Hspan Hrelation)
      as [weights [sc [Hweights [Hpositive [Hcoefficient Hrhs]]]]].
    rewrite Hrelation in Hrhs.
    pose proof (equality_weights_length _ _ Hweights) as Hweight_length.
    destruct (hull_others_length _ _ _ Hnth) as [Hremoved Hprefix].
    assert (Hbound : i <= length weights) by lia.
    set (all_weights := firstn i weights ++ (-sc)%Z :: skipn i weights).
    assert (Hlength : length all_weights = length (affine_hull A B)).
    { unfold all_weights. rewrite hull_insert_length by exact Hbound. lia. }
    assert (Hcoefficients : forall x,
      C.comb_coef (affine_hull A B) all_weights x = 0%Z).
    { intro x. change (row_sum (affine_hull A B) all_weights
        (fun s => C.coef_of x (lhs s)) = 0%Z).
      unfold all_weights. rewrite (hull_insert_sum _ _ _ _ _ _ Hnth Hbound).
      change ((-sc * C.coef_of x (lhs r) +
        C.comb_coef (firstn i (affine_hull A B) ++ skipn (S i) (affine_hull A B))
          weights x)%Z = 0%Z).
      rewrite Hcoefficient. ring. }
    assert (Hright : C.comb_rhs (affine_hull A B) all_weights = 0%Z).
    { change (row_sum (affine_hull A B) all_weights rhs = 0%Z).
      unfold all_weights. rewrite (hull_insert_sum _ _ _ _ _ _ Hnth Hbound).
      change ((-sc * rhs r +
        C.comb_rhs (firstn i (affine_hull A B) ++ skipn (S i) (affine_hull A B))
          weights)%Z = 0%Z).
      rewrite Hrhs. ring. }
    pose proof (hull_affine_zero_weights A B all_weights Hlength Hcoefficients Hright)
      as Hzero.
    assert (Hmember : In (-sc)%Z all_weights).
    { unfold all_weights. apply in_or_app. right. now left. }
    pose proof (proj1 (Forall_forall _ _) Hzero (-sc)%Z Hmember) as Hfalse.
    change ((-sc)%Z = 0%Z) in Hfalse. change (0 < sc)%Z in Hpositive. lia.
  Qed.

  Lemma span_trans : forall a b c, Forall (in_span a) b -> Forall (in_span b) c ->
    Forall (in_span a) c.
  Proof.
    exact span_trans_draft.
  Qed.


  (** Adding source rows preserves their exact span. *)
  Lemma span_weaken : forall A B r, incl A B -> in_span A r -> in_span B r.
  Proof.
    intros A B r Hin Hspan. apply span_trans_row with (B := A); [|exact Hspan].
    apply Forall_forall. intros s Hs. left. now apply Hin.
  Qed.

  (** Every next row is fresh relative to the previously selected equalities. *)
  Fixpoint span_sequence (prefix rows : list (lcons X.t)) : Prop :=
    match rows with
    | [] => True
    | r :: rest => ~ in_span prefix r /\ span_sequence (r :: prefix) rest
    end.

  (** Moving one source from the head past a prefix preserves every member. *)
  Lemma span_move_head_incl : forall (r : lcons X.t) prefix rest,
    incl (r :: prefix ++ rest) (prefix ++ r :: rest).
  Proof.
    intros r prefix rest s [Hsame|Hs].
    - subst s. apply in_or_app. right. now left.
    - apply in_app_or in Hs as [Hs|Hs].
      + apply in_or_app. now left.
      + apply in_or_app. right. now right.
  Qed.

  (** Exclusion from all other rows implies freshness along the entire sequence. *)
  Lemma span_sequence_exclusion : forall rows prefix,
    (forall i r, nth_error rows i = Some r ->
      ~ in_span (prefix ++ firstn i rows ++ skipn (S i) rows) r) ->
    span_sequence prefix rows.
  Proof.
    intro rows. induction rows as [|r rows IH]; intros prefix Hexclude; [exact I|].
    split.
    - intro Hspan. apply (Hexclude 0 r eq_refl).
      apply span_weaken with (A := prefix); [|exact Hspan].
      intros s Hs. apply in_or_app. now left.
    - apply IH. intros i s Hnth Hspan. apply (Hexclude (S i) s Hnth).
      apply span_weaken with (A := (r :: prefix) ++ firstn i rows ++ skipn (S i) rows);
        [|exact Hspan].
      change (incl (r :: prefix ++ (firstn i rows ++ skipn (S i) rows))
        (prefix ++ r :: (firstn i rows ++ skipn (S i) rows))).
      apply span_move_head_incl.
  Qed.

  (** Equal source and multiplier prefixes split a finite row sum. *)
  Lemma row_sum_app : forall A B ms ns entry, length ms = length A ->
    row_sum (A ++ B) (ms ++ ns) entry =
      (row_sum A ms entry + row_sum B ns entry)%Z.
  Proof.
    intro A. induction A as [|p A IH]; intros B [|m ms] ns entry Hlength;
      cbn [length] in Hlength; try discriminate; [reflexivity|].
    change ((m * entry p + row_sum (A ++ B) (ms ++ ns) entry)%Z =
      (m * entry p + row_sum A ms entry + row_sum B ns entry)%Z).
    rewrite IH by lia. ring.
  Qed.

  (** A vector of zero multipliers contributes zero to every row observation. *)
  Lemma row_sum_all_zero : forall P ms entry,
    Forall (fun m => m = 0%Z) ms -> row_sum P ms entry = 0%Z.
  Proof.
    intros P ms entry Hzero. revert P.
    induction Hzero as [|m ms Hm Htail IH]; intros [|p P]; try reflexivity.
    change ((m * entry p + row_sum P ms entry)%Z = 0%Z). rewrite Hm, IH. ring.
  Qed.

  (** Splitting source rows splits their admissible equality multiplier vector. *)
  Lemma equality_weights_cut : forall A B weights,
    equality_weights (A ++ B) weights ->
    exists ms ns, weights = ms ++ ns /\ equality_weights A ms /\ equality_weights B ns.
  Proof.
    intro A. induction A as [|p A IH]; intros B weights Hweights.
    - exists [], weights. split; [reflexivity|]. split; [constructor|exact Hweights].
    - inversion Hweights as [|p' m rows rest Hp Hrest]; subst p' rows.
      destruct (IH B rest Hrest) as [ms [ns [Hsame [Hms Hns]]]].
      subst rest. exists (m :: ms), ns. split; [reflexivity|].
      split; [now constructor|exact Hns].
  Qed.

  (** A nonzero equality multiplier identifies an equality source and its exact position. *)
  Lemma equality_weights_nonzero : forall P weights,
    equality_weights P weights -> ~ Forall (fun m => m = 0%Z) weights ->
    exists left q right before m after,
      P = left ++ q :: right /\ weights = before ++ m :: after /\
      equality_weights left before /\ equality_weights right after /\
      lrel q = REq /\ m <> 0%Z.
  Proof.
    intros P weights Hweights. induction Hweights as [|p m P weights Hp Htail IH];
      intro Hnonzero.
    - exfalso. apply Hnonzero. constructor.
    - destruct (Z.eq_dec m 0) as [Hzero|Hzero].
      + assert (Htail_nonzero : ~ Forall (fun m => m = 0%Z) weights).
        { intro Hz. apply Hnonzero. now constructor. }
        destruct (IH Htail_nonzero) as
          [left [q [right [before [a [after [Hrows [Hmults [Hleft [Hright [Hq Ha]]]]]]]]]]].
        exists (p :: left), q, right, (m :: before), a, after.
        subst P weights. split; [reflexivity|]. split; [reflexivity|].
        split; [now constructor|]. split; [exact Hright|]. now split.
      + exists [], p, P, [], m, weights. split; [reflexivity|].
        split; [reflexivity|]. split; [constructor|]. split; [exact Htail|].
        split; [|exact Hzero]. destruct (lrel p) eqn:Hrel; [reflexivity|].
        exfalso. apply Hzero. now apply Hp.
  Qed.

  (** A certificate with a zero suffix is already a certificate from its prefix. *)
  Lemma equality_certificate_prefix : forall A B r ms ns sc,
    equality_weights A ms -> Forall (fun m => m = 0%Z) ns ->
    equality_certificate (A ++ B) r (ms ++ ns) sc -> equality_certificate A r ms sc.
  Proof.
    intros A B r ms ns sc Hms Hzero [_ [Hscale [Hcoef Hrhs]]].
    pose proof (equality_weights_length _ _ Hms) as Hlength.
    unfold equality_certificate. split; [exact Hms|]. split; [exact Hscale|]. split.
    - intro x. specialize (Hcoef x).
      change (row_sum (A ++ B) (ms ++ ns) (fun p => C.coef_of x (lhs p)) =
        (sc * C.coef_of x (lhs r))%Z) in Hcoef.
      rewrite row_sum_app in Hcoef by lia.
      rewrite (row_sum_all_zero B ns (fun p => C.coef_of x (lhs p)) Hzero),
        Z.add_0_r in Hcoef. exact Hcoef.
    - change (match lrel r with
        | REq => row_sum (A ++ B) (ms ++ ns) rhs = (sc * rhs r)%Z
        | RLe => (row_sum (A ++ B) (ms ++ ns) rhs <= sc * rhs r)%Z
        end) in Hrhs.
      rewrite row_sum_app in Hrhs by lia.
      rewrite (row_sum_all_zero B ns rhs Hzero), Z.add_0_r in Hrhs. exact Hrhs.
  Qed.

  (** Solving a weighted equality for one nonzero source preserves each observation. *)
  Lemma row_sum_exchange : forall P Q r q ms ns m sc sign entry,
    length ms = length P ->
    row_sum (P ++ q :: Q) (ms ++ m :: ns) entry = (sc * entry r)%Z ->
    row_sum (r :: P ++ Q)
      ((sign * sc)%Z :: map (fun a => (-sign * a)%Z) (ms ++ ns)) entry =
      (sign * m * entry q)%Z.
  Proof.
    intros P Q r q ms ns m sc sign entry Hlength Hsum.
    change ((sign * sc * entry r +
      row_sum (P ++ Q) (map (fun a => (-sign * a)%Z) (ms ++ ns)) entry)%Z =
      (sign * m * entry q)%Z).
    rewrite row_sum_scale, row_sum_app by exact Hlength.
    rewrite row_sum_app in Hsum by exact Hlength.
    change ((row_sum P ms entry + (m * entry q + row_sum Q ns entry))%Z =
      (sc * entry r)%Z) in Hsum.
    replace (sign * sc * entry r)%Z with (sign * (sc * entry r))%Z by ring.
    rewrite <- Hsum. ring.
  Qed.

  (** Replacing one nonzero source multiplier by the target yields a reverse certificate. *)
  Lemma equality_certificate_exchange : forall P Q r q ms ns m sc,
    lrel r = REq -> lrel q = REq -> m <> 0%Z ->
    equality_weights P ms -> equality_weights Q ns ->
    equality_certificate (P ++ q :: Q) r (ms ++ m :: ns) sc ->
    exists weights scale, equality_certificate (r :: P ++ Q) q weights scale.
  Proof.
    intros P Q r q ms ns m sc Hr Hq Hnonzero Hms Hns [_ [Hscale [Hcoef Hrhs]]].
    rewrite Hr in Hrhs.
    set (sign := if (m <? 0)%Z then (-1)%Z else 1%Z).
    assert (Hsign : (sign * m)%Z = Z.abs m) by apply coefficient_sign_abs.
    assert (Hpositive : (0 < Z.abs m)%Z) by (destruct m; cbn; lia).
    pose proof (equality_weights_length _ _ Hms) as Hlength.
    exists ((sign * sc)%Z :: map (fun a => (-sign * a)%Z) (ms ++ ns)), (Z.abs m).
    unfold equality_certificate. split.
    - constructor.
      + intro Hkind. rewrite Hr in Hkind. discriminate.
      + apply equality_weights_scale. now apply hull_weights_app.
    - split; [exact Hpositive|]. split.
      + intro x. change (row_sum (r :: P ++ Q)
          ((sign * sc)%Z :: map (fun a => (-sign * a)%Z) (ms ++ ns))
          (fun p => C.coef_of x (lhs p)) = (Z.abs m * C.coef_of x (lhs q))%Z).
        rewrite <- Hsign. exact (row_sum_exchange P Q r q ms ns m sc sign
          (fun p => C.coef_of x (lhs p)) ltac:(lia) (Hcoef x)).
      + rewrite Hq. change (row_sum (r :: P ++ Q)
          ((sign * sc)%Z :: map (fun a => (-sign * a)%Z) (ms ++ ns)) rhs =
          (Z.abs m * rhs q)%Z).
        rewrite <- Hsign. exact (row_sum_exchange P Q r q ms ns m sc sign rhs
          ltac:(lia) Hrhs).
  Qed.

  (** A fresh equality replaces exactly one remaining source without losing the old span. *)
  Lemma span_exchange : forall prefix remaining r,
    lrel r = REq -> ~ in_span prefix r -> in_span (prefix ++ remaining) r ->
    exists rest, S (length rest) = length remaining /\
      Forall (in_span (r :: prefix ++ rest)) (prefix ++ remaining).
  Proof.
    intros prefix remaining r Hr Hfresh Hspan.
    destruct (span_equality_certificate _ r Hspan Hr) as [weights [sc Hcertificate]].
    destruct (equality_weights_cut prefix remaining weights (proj1 Hcertificate))
      as [ms [ns [Hweights [Hms Hns]]]]. subst weights.
    assert (Hnonzero : ~ Forall (fun m => m = 0%Z) ns).
    { intro Hzero. apply Hfresh. apply span_of_certificate with (ms := ms) (sc := sc).
      now apply equality_certificate_prefix with (B := remaining) (ns := ns). }
    destruct (equality_weights_nonzero remaining ns Hns Hnonzero) as
      [left [q [right [before [m [after [Hrows [Hmults [Hleft [Hright [Hq Hm]]]]]]]]]]].
    subst remaining ns. exists (left ++ right). split.
    - rewrite !length_app. cbn [length]. lia.
    - assert (Hback : in_span (r :: prefix ++ (left ++ right)) q).
      { assert (Hcombined : equality_certificate ((prefix ++ left) ++ q :: right) r
          ((ms ++ before) ++ m :: after) sc).
        { rewrite <- !app_assoc. exact Hcertificate. }
        destruct (equality_certificate_exchange (prefix ++ left) right r q
          (ms ++ before) after m sc Hr Hq Hm (hull_weights_app _ _ _ _ Hms Hleft)
          Hright Hcombined) as [back_weights [back_scale Hback]].
        rewrite <- app_assoc in Hback.
        now apply span_of_certificate with (ms := back_weights) (sc := back_scale). }
      apply Forall_forall. intros s Hs. apply in_app_or in Hs as [Hs|Hs].
      + left. right. apply in_or_app. now left.
      + apply in_app_or in Hs as [Hs|[Hsame|Hs]].
        * left. right. apply in_or_app. right. apply in_or_app. now left.
        * subst s. exact Hback.
        * left. right. apply in_or_app. right. apply in_or_app. now right.
  Qed.

  (** Sequential exchange spends one remaining source per independent equality. *)
  Lemma span_exchange_sequence : forall rows prefix remaining,
    span_sequence prefix rows -> Forall (fun r => lrel r = REq) rows ->
    Forall (in_span (prefix ++ remaining)) rows ->
    exists rest, length rows + length rest = length remaining /\
      Forall (in_span (rev rows ++ prefix ++ rest)) (prefix ++ remaining).
  Proof.
    intro rows. induction rows as [|r rows IH]; intros prefix remaining Hsequence Heq Hspan.
    - exists remaining. split; [reflexivity|]. apply Forall_forall. intros s Hs. now left.
    - destruct Hsequence as [Hfresh Hsequence].
      inversion Heq as [|r' rows' Hr Htail_eq]; subst r' rows'.
      inversion Hspan as [|r' rows' Hrow Htail_span]; subst r' rows'.
      destruct (span_exchange prefix remaining r Hr Hfresh Hrow)
        as [middle [Hcount Hforward]].
      assert (Htail : Forall (in_span ((r :: prefix) ++ middle)) rows).
      { apply span_trans with (b := prefix ++ remaining); assumption. }
      destruct (IH (r :: prefix) middle Hsequence Htail_eq Htail)
        as [rest [Hlength Hback]]. exists rest. split.
      + cbn [length]. lia.
      + assert (Hcomposed : Forall (in_span (rev rows ++ (r :: prefix) ++ rest))
          (prefix ++ remaining)).
        { apply span_trans with (b := (r :: prefix) ++ middle); assumption. }
        cbn [rev]. rewrite <- !app_assoc. exact Hcomposed.
  Qed.

  (** Independent equalities cannot outnumber their sources; equal dimensions recover the span. *)
  Lemma span_dimension : forall A rows,
    Forall (fun r => lrel r = REq) rows ->
    (forall i r, nth_error rows i = Some r ->
      ~ in_span (firstn i rows ++ skipn (S i) rows) r) ->
    Forall (in_span A) rows ->
    length rows <= length A /\
      (length A <= length rows -> Forall (in_span rows) A).
  Proof.
    intros A rows Heq Hindependent Hspan.
    assert (Hsequence : span_sequence [] rows).
    { apply span_sequence_exclusion. exact Hindependent. }
    destruct (span_exchange_sequence rows [] A Hsequence Heq Hspan)
      as [rest [Hlength Hback]]. split; [lia|]. intro Hdim.
    assert (Hrest : rest = []).
    { destruct rest; [reflexivity|]. cbn [length] in Hlength. lia. }
    subst rest. rewrite !app_nil_r in Hback.
    eapply Forall_impl; [|exact Hback]. intros r Hr.
    apply span_weaken with (A := rev rows); [|exact Hr].
    intros s Hs. exact (proj2 (in_rev rows s) Hs).
  Qed.

  (** A hull cannot gain rank, and equal rank forces the right input below the left. *)
  Lemma affine_hull_rank : forall A B,
    length (affine_hull A B) <= length A /\
      (length A <= length (affine_hull A B) -> leb (Reached B) (Reached A) = true).
  Proof.
    intros A B. destruct (join_span A B (affine_hull A B) eq_refl) as [Hleft Hright].
    destruct (span_dimension A (affine_hull A B)
      (join_eq A B (affine_hull A B) eq_refl)
      (join_independent A B (affine_hull A B) eq_refl) Hleft) as [Hlength Hreverse].
    split; [exact Hlength|]. intro Hdim. apply leb_complete_span.
    apply span_trans with (b := affine_hull A B); [exact Hright|now apply Hreverse].
  Qed.

  (** Every changing widening strictly decreases the number of stored source rows. *)
  Lemma wrank_widen_checked : forall p a b, is_bot a = false -> leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Proof.
    intros p a b Hbot Hle. destruct a as [|A]; [discriminate|].
    destruct b as [|B]; [discriminate|]. unfold widen. rewrite Hle.
    change (length (affine_hull A B) < length A).
    destruct (affine_hull_rank A B) as [Hlength Hreverse].
    destruct (Nat.lt_ge_cases (length (affine_hull A B)) (length A)) as [Hlt|Hge];
      [exact Hlt|]. pose proof (Hreverse Hge). congruence.
  Qed.

  (** Stable widenings retain rank and changing widenings strictly lower it. *)
  Lemma wrank_widen_le_checked : forall p a b, is_bot a = false ->
    wrank p (widen p a b) <= wrank p a.
  Proof.
    intros p a b Hbot. destruct (leb b a) eqn:Hle.
    - unfold widen. rewrite Hle. lia.
    - pose proof (wrank_widen_checked p a b Hbot Hle). lia.
  Qed.

  Lemma wrank_widen : forall p a b, is_bot a = false -> leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Proof.
    exact wrank_widen_checked.
  Qed.
  Lemma wrank_widen_le : forall p a b, is_bot a = false -> wrank p (widen p a b) <= wrank p a.
  Proof.
    exact wrank_widen_le_checked.
  Qed.
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
  (** Every bound checked against prepared rows holds for the original affine state. *)
  Lemma range_linear_sound : forall P f v, Forall (sat v) P ->
    in_bnd (fst (range_linear P f)) (snd (range_linear P f)) (eval_lin v f).
  Proof.
    intros P f v Hmodels. unfold range_linear.
    set (prepared := map normalize_row P).
    assert (Hprepared : Forall (sat v) prepared).
    { unfold prepared. now apply normalize_rows_sat. }
    set (xs := variables (LCons X.t (coef f) REq 0 :: prepared)).
    set (r := karr_target (equality_basis xs prepared) 1
      (KRow (map (fun x => coefficient x (coef f)) xs) 0
        (repeat 0%Z (length prepared)) 1)).
    set (z := (- kright r / kscale r + cst f)%Z).
    destruct (entail_cert prepared (LCons X.t (coef f) REq (z - cst f)%Z))
      as [certificate|] eqn:Hcertificate; [|split; exact I].
    pose proof (C.check_entails_sound prepared _ certificate
      (entail_cert_checked prepared _ certificate Hcertificate) v Hprepared) as Hbound.
    cbn [sat lrel lhs rhs] in Hbound.
    change (z <= eval_lin v f <= z)%Z. unfold eval_lin. lia.
  Qed.

  (** Linearization transfers the prepared affine range back to the expression value. *)
  Lemma range_sound : forall e s st c,
    ngamma s (fun y => N.num (st y)) -> eval_term L.eval st e = Some c ->
    in_bnd (fst (range e s)) (snd (range e s)) (N.num c).
  Proof.
    intros e [|P] st c Hmodels Heval; [contradiction|]. unfold range.
    destruct (F.lin_of e) as [[f wrapping]|] eqn:Hform; [destruct wrapping|];
      try solve [split; exact I].
    pose proof (F.lin_sound st e c f NoWrap Heval Hform) as Hvalue.
    cbn [wrap_into] in Hvalue. rewrite Hvalue. now apply range_linear_sound.
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
  TimeFun scale_coef.
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
  TimeFun range_linear.
  TimeFun range.

  (** The aggregate coefficient list has exactly the concrete-update evaluation. *)
  Lemma subst_eval : forall v x f r,
    eval_coef v (lhs (subst x f r)) =
      (eval_coef (upd X.eqb v x (eval_lin v f)) (lhs r) -
        coefficient x (lhs r) * cst f)%Z.
  Proof.
    intros v x f r. unfold subst, scale_coef. cbn [normalize_row lhs].
    rewrite normalize_coef_eval, eval_coef_app, eval_coef_scale,
      eval_coef_without, eval_coef_update. unfold eval_lin. ring.
  Qed.

  (** Aggregating repeated occurrences preserves the frozen substitution meaning. *)
  Lemma subst_sat_checked : forall v x f r,
    sat v (subst x f r) <-> sat (upd X.eqb v x (eval_lin v f)) r.
  Proof.
    intros v x f r. unfold sat. rewrite subst_eval.
    unfold subst. cbn [normalize_row lrel rhs]. destruct (lrel r); lia.
  Qed.

  (** Magnitude supplies the shared binary-size estimates. *)
  Definition karr_magnitude (z : Z) : nat := Z.to_nat (Z.abs z).

  (** An integer magnitude is strictly below the power determined by its binary width. *)
  Lemma karr_magnitude_upper : forall z, karr_magnitude z < 2 ^ Z.size_nat z.
  Proof.
    intros [|p|p].
    - change (0 < 1). lia.
    - exact (Pos.size_nat_upper p).
    - exact (Pos.size_nat_upper p).
  Qed.

  (** A strict power-of-two bound bounds an integer's binary width. *)
  Lemma karr_size_least : forall z k, karr_magnitude z < 2 ^ k -> Z.size_nat z <= k.
  Proof.
    intros [|p|p] k Hbound; cbn [karr_magnitude Z.abs Z.to_nat Z.size_nat] in *;
      try lia; now apply Pos.size_nat_least.
  Qed.

  (** The magnitude of a sum is at most the sum of its magnitudes. *)
  Lemma karr_magnitude_add : forall x y,
    karr_magnitude (x + y) <= karr_magnitude x + karr_magnitude y.
  Proof.
    intros x y. unfold karr_magnitude.
    rewrite <- Z2Nat.inj_add by apply Z.abs_nonneg.
    apply Z2Nat.inj_le; try apply Z.abs_nonneg; try lia.
  Qed.

  (** Addition uses at most one bit beyond the wider operand. *)
  Lemma karr_size_add : forall x y,
    Z.size_nat (x + y) <= Nat.max (Z.size_nat x) (Z.size_nat y) + 1.
  Proof.
    intros x y. apply karr_size_least.
    pose proof (karr_magnitude_upper x) as Hx.
    pose proof (karr_magnitude_upper y) as Hy.
    pose proof (karr_magnitude_add x y) as Hsum.
    set (bits := Nat.max (Z.size_nat x) (Z.size_nat y)).
    assert (Hxp : 2 ^ Z.size_nat x <= 2 ^ bits).
    { apply Nat.pow_le_mono_r; unfold bits; lia. }
    assert (Hyp : 2 ^ Z.size_nat y <= 2 ^ bits).
    { apply Nat.pow_le_mono_r; unfold bits; lia. }
    replace (bits + 1) with (S bits) by lia. rewrite Nat.pow_succ_r by lia. lia.
  Qed.

  (** A product uses at most the combined widths of its operands. *)
  Lemma karr_size_mul : forall x y,
    Z.size_nat (x * y) <= Z.size_nat x + Z.size_nat y.
  Proof.
    intros [|p|p] [|q|q]; cbn [Z.mul Z.size_nat]; try lia; apply Pos.size_nat_mul.
  Qed.

  (** Negation preserves an integer's binary width. *)
  Lemma karr_size_opp : forall z, Z.size_nat (- z) = Z.size_nat z.
  Proof.
    intros [|p|p]; reflexivity.
  Qed.

  (** Absolute value preserves an integer's binary width. *)
  Lemma karr_size_abs : forall z, Z.size_nat (Z.abs z) = Z.size_nat z.
  Proof.
    intros [|p|p]; reflexivity.
  Qed.


  (** Set bits pay for carries during positive multiplication. *)
  Fixpoint karr_mul_ones_count (p : positive) : N :=
    match p with
    | xI q => (karr_mul_ones_count q + 1)%N
    | xO q => karr_mul_ones_count q
    | xH => 1%N
    end.

  (** A positive integer has no more set bits than binary digits. *)
  Lemma karr_mul_ones_count_le : forall p, (karr_mul_ones_count p <= N.of_nat (Pos.size_nat p))%N.
  Proof.
    induction p as [p IH|p IH|]; time_cbn; lia.
  Qed.

  (** A successor pays for every carry by removing set bits. *)
  Lemma karr_T_succ_ones : forall p,
    (Pos.T_succ p + karr_mul_ones_count (Pos.succ p) <= karr_mul_ones_count p + 2)%N.
  Proof.
    induction p as [p IH|p IH|]; time_unfold Pos.T_succ; time_cbn; lia.
  Qed.

  (** Addition charges the first operand's digits and the change of set-bit potential. *)
  Lemma karr_T_add_ones_both : forall p q,
    (Pos.T_add p q + karr_mul_ones_count (Pos.add p q) <=
      3 * N.of_nat (Pos.size_nat p) + karr_mul_ones_count q + 3)%N /\
    (Pos.T_add_carry p q + karr_mul_ones_count (Pos.add_carry p q) <=
      3 * N.of_nat (Pos.size_nat p) + karr_mul_ones_count q + 3)%N.
  Proof.
    intro p. induction p as [p IH|p IH|]; intros [q|q|];
      time_unfold Pos.T_add; time_unfold Pos.T_add_carry; time_cbn;
      try specialize (IH q);
      try pose proof (karr_T_succ_ones p); try pose proof (karr_T_succ_ones q);
      try pose proof (karr_mul_ones_count_le p); try pose proof (karr_mul_ones_count_le q); lia.
  Qed.

  (** Shift-and-add multiplication amortizes its internal carry chains. *)
  Lemma karr_T_mul_ones : forall p q,
    (Pos.T_mul p q + karr_mul_ones_count (Pos.mul p q) <=
      6 * N.of_nat (Pos.size_nat p) * (N.of_nat (Pos.size_nat q) + 1) + karr_mul_ones_count q)%N.
  Proof.
    intro p. induction p as [p IH|p IH|]; intro q;
      time_unfold Pos.T_mul; time_cbn; try specialize (IH q).
    - pose proof (proj1 (karr_T_add_ones_both q (xO (Pos.mul p q)))) as Hadd.
      time_cbn_all. nia.
    - nia.
    - nia.
  Qed.

  (** Positive multiplication is bilinear in operand bit lengths. *)
  Lemma karr_T_pos_mul_bilinear : forall p q,
    (Pos.T_mul p q <=
      7 * N.of_nat (Pos.size_nat p) * (N.of_nat (Pos.size_nat q) + 1))%N.
  Proof.
    intros p q. pose proof (karr_T_mul_ones p q) as Hmul.
    pose proof (karr_mul_ones_count_le q) as Hones.
    pose proof (Pos.size_nat_pos p) as Hpositive. nia.
  Qed.

  (** Signed multiplication has the same bilinear bound with its sign dispatch. *)
  Lemma karr_T_Z_mul_bilinear : forall x y,
    (Z.T_mul x y <=
      8 * N.of_nat (Z.size_nat x + 1) * N.of_nat (Z.size_nat y + 1))%N.
  Proof.
    intros [|p|p] [|q|q]; time_unfold Z.T_mul; time_cbn;
      try pose proof (karr_T_pos_mul_bilinear p q); nia.
  Qed.


  (** Mapping charges only callbacks on actual list members. *)
  Lemma karr_T_map_members : forall (A B : Type) (f : A -> B) (T_f : A -> N) k xs,
    (forall x, In x xs -> (T_f x <= k)%N) ->
    (ListDef.T_map f T_f xs <= (k + 1) * N.of_nat (length xs) + 1)%N.
  Proof.
    intros A B f T_f k xs. induction xs as [|x xs IH]; intro Hcallback.
    - time_unfold ListDef.T_map. time_cbn. lia.
    - pose proof (Hcallback x (or_introl eq_refl)) as Hhead.
      specialize (IH ltac:(intros y Hin; apply Hcallback; now right)).
      time_unfold ListDef.T_map. time_cbn. nia.
  Qed.

  (** Filtering also needs callback bounds only on its actual input list. *)
  Lemma karr_T_filter_members : forall A (f : A -> bool) (T_f : A -> N) k xs,
    (forall x, In x xs -> (T_f x <= k)%N) ->
    (List.T_filter f T_f xs <= (k + 1) * N.of_nat (length xs) + 1)%N.
  Proof.
    intros A f T_f k xs. induction xs as [|x xs IH]; intro Hcallback.
    - time_unfold List.T_filter. time_cbn. lia.
    - pose proof (Hcallback x (or_introl eq_refl)) as Hhead.
      specialize (IH ltac:(intros y Hin; apply Hcallback; now right)).
      time_unfold List.T_filter. destruct (f x); time_cbn; nia.
  Qed.


  (** Two bounded factors fit the same quadratic clock envelope. *)
  Lemma karr_clock_product_bound : forall cost factor a b size left right,
    (cost <= factor * a * b)%N -> (a <= left * size)%N ->
    (b <= right * size)%N ->
    (cost <= (factor * left * right) * (size * size))%N.
  Proof.
    intros cost factor a b size left right Hcost Ha Hb.
    eapply N.le_trans; [exact Hcost|].
    replace (factor * a * b)%N with (factor * (a * b))%N by ring.
    replace ((factor * left * right) * (size * size))%N with
      (factor * ((left * size) * (right * size)))%N by ring.
    apply N.mul_le_mono_l. now apply N.mul_le_mono.
  Qed.

  (** Conversion preserves a natural-number square as one binary product. *)
  Lemma karr_nat_square : forall n,
    N.of_nat (n^2) = (N.of_nat n * N.of_nat n)%N.
  Proof.
    intro n. change (N.of_nat (n * (n * 1)) = (N.of_nat n * N.of_nat n)%N).
    rewrite Nat.mul_1_r. apply Nat2N.inj_mul.
  Qed.

  (** A positive extent is bounded by its square. *)
  Lemma karr_nat_square_ge : forall n, 1 <= n ->
    (N.of_nat n <= N.of_nat (n^2))%N.
  Proof.
    intros n Hpositive. rewrite karr_nat_square.
    replace (N.of_nat n) with (N.of_nat n * 1)%N at 1 by ring.
    apply N.mul_le_mono_l. lia.
  Qed.


  (** Every collected value is paid by a visited trie node. *)
  Lemma karr_values_ne_length : forall A (tr : trie_ne A) acc,
    length (karr_values_ne tr acc) <= PTrie.nodes_ne tr + length acc.
  Proof.
    intros A tr. induction tr as
      [r IHr|a|a r IHr|l IHl|l IHl r IHr|l IHl a|l IHl a r IHr]; intro acc;
      cbn [karr_values_ne PTrie.nodes_ne length].
    - specialize (IHr acc). lia.
    - lia.
    - specialize (IHr acc). lia.
    - specialize (IHl acc). lia.
    - specialize (IHl (karr_values_ne r acc)). specialize (IHr acc). lia.
    - specialize (IHl (a :: acc)). cbn [length] in IHl. lia.
    - specialize (IHl (a :: karr_values_ne r acc)). specialize (IHr acc).
      cbn [length] in IHl. lia.
  Qed.

  (** Collecting values performs only a constant amount of work at each node. *)
  Lemma T_karr_values_ne_bounded : forall A (tr : trie_ne A) acc,
    (@T_karr_values_ne A tr acc <= 3 * N.of_nat (PTrie.nodes_ne tr))%N.
  Proof.
    intros A tr. induction tr as
      [r IHr|a|a r IHr|l IHl|l IHl r IHr|l IHl a|l IHl a r IHr]; intro acc;
      time_unfold (@T_karr_values_ne); cbn [PTrie.nodes_ne]; time_simpl.
    - specialize (IHr acc). lia.
    - lia.
    - specialize (IHr acc). lia.
    - specialize (IHl acc). lia.
    - specialize (IHl (karr_values_ne r acc)). specialize (IHr acc). lia.
    - specialize (IHl (a :: acc)). lia.
    - specialize (IHl (a :: karr_values_ne r acc)). specialize (IHr acc). lia.
  Qed.

  (** The complete value list is no longer than the coefficient trie. *)
  Lemma karr_values_length : forall A (tr : ptrie A),
    length (karr_values tr) <= PTrie.nodes tr.
  Proof.
    intros A [|tr]; [reflexivity|].
    pose proof (karr_values_ne_length A tr []).
    cbn [karr_values PTrie.nodes length] in *. lia.
  Qed.

  (** Dispatching to the nonempty traversal adds one constant charge. *)
  Lemma T_karr_values_bounded : forall A (tr : ptrie A),
    (@T_karr_values A tr <= 4 * N.of_nat (PTrie.nodes tr + 1))%N.
  Proof.
    intros A [|tr]; time_unfold (@T_karr_values); cbn [PTrie.nodes]; time_simpl.
    - lia.
    - pose proof (T_karr_values_ne_bounded A tr []). lia.
  Qed.

  (** A proof model reads the current coefficient stored at one key. *)
  Definition karr_previous (m : ptrie (X.t * Z)) (x : X.t) : Z :=
    match PTrieCode.get (X.encode x) m with Some p => snd p | None => 0%Z end.

  (** A coefficient table has one common arithmetic-width bound. *)
  Definition karr_accum_values_bits (m : ptrie (X.t * Z)) (bits : nat) : Prop :=
    forall key p, PTrieCode.get key m = Some p -> Z.size_nat (snd p) <= bits.

  (** Reading a bounded table preserves its arithmetic-width bound. *)
  Lemma karr_previous_bits : forall m bits x,
    karr_accum_values_bits m bits -> Z.size_nat (karr_previous m x) <= bits.
  Proof.
    intros m bits x Hbits. unfold karr_previous.
    destruct (PTrieCode.get (X.encode x) m) as [p|] eqn:Hget.
    - exact (Hbits _ p Hget).
    - change (0 <= bits). lia.
  Qed.

  (** One signed insertion increases the common width by at most one. *)
  Lemma karr_add_term_values_bits : forall m p bits,
    karr_accum_values_bits m bits -> Z.size_nat (snd p) <= bits ->
    karr_accum_values_bits (add_term m p) (bits + 1).
  Proof.
    intros m p bits Hvalues Hp key q Hget. unfold add_term in Hget.
    destruct (PTrieCode.get (X.encode (fst p)) m) as [old|] eqn:Hold;
      destruct (Pos.eq_dec key (X.encode (fst p))) as [Hsame|Hother].
    - subst key. rewrite PTrie.get_set_same in Hget. injection Hget as Hsame. subst q.
      cbn [snd]. pose proof (karr_size_add (snd old) (snd p)).
      pose proof (Hvalues _ old Hold). lia.
    - rewrite PTrie.get_set_other in Hget by exact Hother.
      pose proof (Hvalues key q Hget). lia.
    - subst key. rewrite PTrie.get_set_same in Hget. injection Hget as Hsame. subst q. lia.
    - rewrite PTrie.get_set_other in Hget by exact Hother.
      pose proof (Hvalues key q Hget). lia.
  Qed.

  (** Inserting one coefficient creates at most one node per encoded key bit. *)
  Lemma karr_add_term_nodes : forall m p,
    PTrie.nodes (add_term m p) <= PTrie.nodes m + Pos.size_nat (X.encode (fst p)).
  Proof.
    intros m p. unfold add_term.
    destruct (PTrieCode.get (X.encode (fst p)) m); apply PTrie.nodes_set.
  Qed.

  (** Summed key widths bound the size of the accumulated trie. *)
  Lemma karr_accum_nodes : forall xs m keys,
    Forall (fun p => Pos.size_nat (X.encode (fst p)) <= keys) xs ->
    PTrie.nodes (fold_left add_term xs m) <= PTrie.nodes m + length xs * keys.
  Proof.
    intro xs. induction xs as [|p xs IH]; intros m keys Hkeys; cbn [fold_left length].
    - lia.
    - inversion Hkeys as [|q qs Hp Htail]; subst q qs.
      specialize (IH (add_term m p) keys Htail).
      pose proof (karr_add_term_nodes m p). lia.
  Qed.

  (** Each insertion charges encoding, two trie paths, and a signed addition. *)
  Definition karr_add_factor : N := (X.c_key + 2 * PTrieT.c_trie + 32)%N.

  (** Insertion time is linear in key width and the two summand widths. *)
  Lemma T_karr_add_term_bounded : forall m p keys bits old,
    Pos.size_nat (X.encode (fst p)) <= keys -> Z.size_nat (snd p) <= bits ->
    Z.size_nat (karr_previous m (fst p)) <= old ->
    (T_add_term m p <= karr_add_factor * N.of_nat (keys + bits + old + 1))%N.
  Proof.
    intros m p keys bits old Hkey Hbits Hold.
    pose proof (X.T_encode_le (fst p)) as Hencode.
    pose proof (PTrieT.T_get_le (X.t * Z) (X.encode (fst p)) m) as Hget.
    time_unfold T_add_term.
    destruct (PTrieCode.get (X.encode (fst p)) m) as [q|] eqn:Hvalue.
    - pose proof (PTrieT.T_set_le (X.t * Z) (X.encode (fst p))
        (fst q, (snd q + snd p)%Z) m) as Hset.
      pose proof (Z.T_add_le (snd q) (snd p)) as Hadd.
      unfold karr_previous in Hold. rewrite Hvalue in Hold.
      unfold karr_add_factor, X.bits in *. time_simpl. nia.
    - pose proof (PTrieT.T_set_le (X.t * Z) (X.encode (fst p)) p m) as Hset.
      unfold karr_add_factor, X.bits in *. time_simpl. nia.
  Qed.

  (** The remaining list length pays for every intermediate signed-sum width. *)
  Lemma T_karr_accum_raw : forall xs m keys bits,
    Forall (fun p => Pos.size_nat (X.encode (fst p)) <= keys /\
      Z.size_nat (snd p) <= bits) xs -> karr_accum_values_bits m bits ->
    (List.T_fold_left add_term T_add_term xs m <=
      (karr_add_factor + 1) * N.of_nat (length xs) *
        N.of_nat (keys + 2 * bits + 2 * length xs + 1) + 1)%N.
  Proof.
    intro xs. induction xs as [|p xs IH]; intros m keys bits Hsizes Hvalues.
    - time_unfold List.T_fold_left. cbn [length]. nia.
    - inversion Hsizes as [|q qs [Hkey Hbits] Htail]; subst q qs.
      assert (Hnext : Forall (fun p => Pos.size_nat (X.encode (fst p)) <= keys /\
        Z.size_nat (snd p) <= bits + 1) xs).
      { eapply Forall_impl; [|exact Htail]. intros q [Hqkey Hqbits]. split; lia. }
      pose proof (karr_add_term_values_bits m p bits Hvalues Hbits) as Hnewvalues.
      specialize (IH (add_term m p) keys (bits + 1) Hnext Hnewvalues).
      pose proof (T_karr_add_term_bounded m p keys bits bits Hkey Hbits
        (karr_previous_bits m bits (fst p) Hvalues)) as Hhead.
      time_unfold List.T_fold_left. cbn [length]. time_simpl.
      rewrite !Nat2N.inj_add, !Nat2N.inj_mul in *. cbn [N.of_nat] in *. nia.
  Qed.

  (** Testing an integer against zero does not traverse its magnitude. *)
  Lemma T_karr_zero_test : forall z, (Z.T_eqb z 0 <= 2)%N.
  Proof.
    intros [|p|p]; time_unfold Z.T_eqb; time_simpl; lia.
  Qed.

  (** The coefficient filter retains exactly the nonzero entries. *)
  Definition karr_nonzero (p : X.t * Z) : bool := negb (Z.eqb (snd p) 0).

  TimeFun karr_nonzero.

  (** Each nonzero test has a fixed callback charge. *)
  Lemma T_karr_nonzero_bounded : forall p, (T_karr_nonzero p <= 6)%N.
  Proof.
    intro p. pose proof (T_karr_zero_test (snd p)).
    time_unfold T_karr_nonzero. time_simpl. lia.
  Qed.

  (** Raw normalization pays the signed accumulation and two linear trie traversals. *)
  Definition karr_raw_normal_factor : N := (4 * (karr_add_factor + 1) + 64)%N.

  (** The raw normalizer is quadratic in occurrence count and linear in initial width. *)
  Lemma T_karr_normal_raw : forall xs keys bits,
    Forall (fun p => Pos.size_nat (X.encode (fst p)) <= keys /\
      Z.size_nat (snd p) <= bits) xs ->
    (T_normalize_coef xs <= karr_raw_normal_factor * N.of_nat (length xs + 1) *
      N.of_nat (keys + 2 * bits + 2 * length xs + 1))%N.
  Proof.
    intros xs keys bits Hsizes.
    assert (Hempty : karr_accum_values_bits PTrieCode.empty bits).
    { intros key p Hget. rewrite PTrie.get_empty in Hget. discriminate. }
    pose proof (T_karr_accum_raw xs PTrieCode.empty keys bits Hsizes Hempty) as Haccum.
    set (tr := fold_left add_term xs PTrieCode.empty).
    assert (Hkeys : Forall (fun p => Pos.size_nat (X.encode (fst p)) <= keys) xs).
    { eapply Forall_impl; [|exact Hsizes]. intros p [Hp _]. exact Hp. }
    pose proof (karr_accum_nodes xs PTrieCode.empty keys Hkeys) as Hnodes.
    change (PTrie.nodes tr <= length xs * keys) in Hnodes.
    pose proof (T_karr_values_bounded (X.t * Z) tr) as Hvalues.
    pose proof (karr_values_length (X.t * Z) tr) as Hlength.
    pose proof (karr_T_filter_members (X.t * Z) karr_nonzero T_karr_nonzero 6
      (karr_values tr) (fun p _ => T_karr_nonzero_bounded p)) as Hfilter.
    time_unfold T_normalize_coef. fold tr.
    change (fun p : X.t * Z => negb (Z.eqb (snd p) 0)) with karr_nonzero.
    time_simpl.
    change (fun (m : ptrie (X.t * Z)) (p : X.t * Z) => T_add_term m p) with T_add_term.
    lazymatch goal with
    | |- context [List.T_filter karr_nonzero ?Tf (karr_values tr)] =>
      change Tf with T_karr_nonzero
    end.
    unfold karr_raw_normal_factor. nia.
  Qed.
  (** Raw repeated coefficients gain at most one bit per occurrence. *)
  Lemma karr_raw_coefficient_bits : forall x xs bits,
    Forall (fun p => Z.size_nat (snd p) <= bits) xs ->
    Z.size_nat (coefficient x xs) <= length xs + bits.
  Proof.
    intros x xs. induction xs as [|[y a] xs IH]; intros bits Hsizes.
    - change (0 <= 0 + bits). lia.
    - inversion Hsizes as [|p ps Ha Htail]; subst p ps.
      rewrite coefficient_cons. cbn [length]. destruct (X.eqb x y).
      + pose proof (karr_size_add a (coefficient x xs)).
        specialize (IH bits Htail). cbn [snd] in Ha. lia.
      + rewrite Z.add_0_l. specialize (IH bits Htail). lia.
  Qed.

  (** Each lookup step compares the query key and adds a matching occurrence. *)
  Definition karr_coefficient_step (x : X.t) (p : X.t * Z) (z : Z) : Z :=
    if X.eqb x (fst p) then (snd p + z)%Z else z.

  TimeFun karr_coefficient_step.

  (** The named lookup step is the executable coefficient fold. *)
  Lemma karr_coefficient_step_fold : forall x xs,
    fold_right (karr_coefficient_step x) 0%Z xs = coefficient x xs.
  Proof.
    reflexivity.
  Qed.

  (** A lookup step has one key comparison and one bounded signed addition. *)
  Definition karr_coefficient_factor : N := (X.c_key + 16)%N.

  (** The query's declared bit count pays for comparison in its actual argument order. *)
  Lemma T_karr_coefficient_step_bounded : forall x p z bits old,
    Z.size_nat (snd p) <= bits -> Z.size_nat z <= old ->
    (T_karr_coefficient_step x p z <=
      karr_coefficient_factor * N.of_nat (X.bits x + bits + old + 1))%N.
  Proof.
    intros x p z bits old Hbits Hold.
    pose proof (X.T_eqb_le x (fst p)) as Heqb.
    pose proof (Z.T_add_le (snd p) z) as Hadd.
    time_unfold T_karr_coefficient_step. unfold karr_coefficient_factor.
    destruct (X.eqb x (fst p)); time_simpl; nia.
  Qed.

  (** The lookup clock accounts for each suffix's growing coefficient sum. *)
  Lemma T_karr_coefficient_fold : forall x xs bits,
    Forall (fun p => Z.size_nat (snd p) <= bits) xs ->
    (List.T_fold_right (karr_coefficient_step x) (T_karr_coefficient_step x) 0%Z xs <=
      (karr_coefficient_factor + 1) * N.of_nat (length xs + 1) *
        N.of_nat (X.bits x + 2 * bits + length xs + 1))%N.
  Proof.
    intros x xs. induction xs as [|p xs IH]; intros bits Hsizes.
    - time_unfold List.T_fold_right. cbn [length]. unfold karr_coefficient_factor. nia.
    - inversion Hsizes as [|q qs Hp Htail]; subst q qs.
      specialize (IH bits Htail).
      assert (Hsum : Z.size_nat (fold_right (karr_coefficient_step x) 0%Z xs) <=
        length xs + bits).
      { rewrite karr_coefficient_step_fold. now apply karr_raw_coefficient_bits. }
      pose proof (T_karr_coefficient_step_bounded x p
        (fold_right (karr_coefficient_step x) 0%Z xs)
        bits (length xs + bits) Hp Hsum) as Hhead.
      time_unfold List.T_fold_right. cbn [length]. time_simpl.
      rewrite !Nat2N.inj_add, !Nat2N.inj_mul in *. cbn [N.of_nat] in *. nia.
  Qed.

  (** The coefficient wrapper adds only a fixed charge to its bounded fold. *)
  Lemma T_karr_coefficient_bounded : forall x xs bits,
    Forall (fun p => Z.size_nat (snd p) <= bits) xs ->
    (T_coefficient x xs <= (karr_coefficient_factor + 4) *
      N.of_nat (length xs + 1) * N.of_nat (X.bits x + 2 * bits + length xs + 1))%N.
  Proof.
    intros x xs bits Hsizes.
    pose proof (T_karr_coefficient_fold x xs bits Hsizes) as Hfold.
    time_unfold T_coefficient.
    change (fun p z => if X.eqb x (fst p) then (snd p + z)%Z else z)
      with (karr_coefficient_step x).
    time_simpl.
    lazymatch goal with
    | |- context [List.T_fold_right (karr_coefficient_step x) ?Tf 0%Z xs] =>
      change Tf with (T_karr_coefficient_step x)
    end.
    assert (Hmass : (1 <= N.of_nat (length xs + 1) *
      N.of_nat (X.bits x + 2 * bits + length xs + 1))%N).
    { change (1 * 1 <= N.of_nat (length xs + 1) *
        N.of_nat (X.bits x + 2 * bits + length xs + 1))%N.
      apply N.mul_le_mono; lia. }
    nia.
  Qed.

  (** A list maximum bounds every mapped member. *)
  Lemma karr_max_member : forall A (f : A -> nat) seed xs x,
    In x xs -> f x <= fold_right Nat.max seed (map f xs).
  Proof.
    intros A f seed xs. induction xs as [|p xs IH]; intros x Hin;
      cbn [In map fold_right] in *; [contradiction|].
    destruct Hin as [Hsame|Hin]; [subst p; lia|]. specialize (IH x Hin). lia.
  Qed.

  (** A list maximum also bounds its initial value. *)
  Lemma karr_max_seed : forall xs seed, seed <= fold_right Nat.max seed xs.
  Proof.
    intro xs. induction xs as [|x xs IH]; intro seed; cbn [fold_right]; [lia|].
    specialize (IH seed). lia.
  Qed.

  (** Every stored key fits its row's declared key width. *)
  Lemma karr_row_key_member : forall r p, In p (lhs r) ->
    Pos.size_nat (X.encode (fst p)) <= C.row_key_bits r.
  Proof.
    intros r p Hin. unfold C.row_key_bits.
    exact (karr_max_member _ (fun q => Pos.size_nat (X.encode (fst q))) 0
      (lhs r) p Hin).
  Qed.

  (** Every stored coefficient fits its row's declared arithmetic width. *)
  Lemma karr_row_entry_bits : forall r p, In p (lhs r) ->
    Z.size_nat (snd p) <= C.row_bits r.
  Proof.
    intros r p Hin. unfold C.row_bits.
    exact (karr_max_member _ (fun q => Z.size_nat (snd q))
      (Z.size_nat (rhs r)) (lhs r) p Hin).
  Qed.

  (** A row's constant fits the same arithmetic-width declaration. *)
  Lemma karr_row_rhs_bits : forall r, Z.size_nat (rhs r) <= C.row_bits r.
  Proof.
    intro r. unfold C.row_bits. apply karr_max_seed.
  Qed.

  (** A raw source row supplies both uniform occurrence bounds. *)
  Lemma karr_row_entry_sizes : forall r,
    Forall (fun p => Pos.size_nat (X.encode (fst p)) <= C.row_key_bits r /\
      Z.size_nat (snd p) <= C.row_bits r) (lhs r).
  Proof.
    intro r. apply Forall_forall. intros p Hin. split.
    - now apply karr_row_key_member with (r := r).
    - now apply karr_row_entry_bits with (r := r).
  Qed.

  (** Summing a raw row's repeated coefficients adds at most its occurrence count in bits. *)
  Lemma karr_raw_row_coefficient_bits : forall x r,
    Z.size_nat (coefficient x (lhs r)) <= length (lhs r) + C.row_bits r.
  Proof.
    intros x r. apply karr_raw_coefficient_bits. apply Forall_forall.
    intros p Hin. now apply karr_row_entry_bits with (r := r).
  Qed.

  (** Public row size dominates its length and both declared input widths. *)
  Lemma karr_lsize_parts : forall r,
    length (lhs r) + C.row_key_bits r + C.row_bits r + 1 <= C.lsize r /\
    (length (lhs r) + 1) * (C.row_bits r + 1) <= C.lsize r /\
    (length (lhs r) + 1) * (C.row_key_bits r + 1) <= C.lsize r.
  Proof.
    intro r. unfold C.lsize. nia.
  Qed.

  (** Scaling charges one bilinear multiplication for each form occurrence. *)
  Lemma T_karr_scale_coef_bounded : forall a xs bits,
    Forall (fun p => Z.size_nat (snd p) <= bits) xs ->
    (T_scale_coef a xs <=
      16 * N.of_nat ((length xs + 1) * (Z.size_nat a + 1) * (bits + 1)))%N.
  Proof.
    intros a xs bits Hbits. time_unfold T_scale_coef.
    lazymatch goal with
    | |- context [ListDef.T_map ?f ?Tf xs] =>
      assert (Hmap : (ListDef.T_map f Tf xs <=
        (12 * N.of_nat ((Z.size_nat a + 1) * (bits + 1)) + 1) *
        N.of_nat (length xs) + 1)%N);
      [ apply karr_T_map_members; intros [x z] Hin;
        pose proof (proj1 (Forall_forall _ _) Hbits (x, z) Hin) as Hz;
        pose proof (karr_T_Z_mul_bilinear a z);
        time_simpl; time_cbn_all; nia
      | nia ]
    end.
  Qed.

  (** Substitution removes every source occurrence of its selected key. *)
  Definition karr_without_key (x : X.t) (p : X.t * Z) : bool :=
    negb (X.eqb (fst p) x).

  TimeFun karr_without_key.

  (** Retention tests charge the stored key in the comparison's actual argument order. *)
  Lemma T_karr_without_key_le : forall x p keys,
    Pos.size_nat (X.encode (fst p)) <= keys ->
    (T_karr_without_key x p <= (X.c_key + 4) * N.of_nat (keys + 1))%N.
  Proof.
    intros x p keys Hkey. pose proof (X.T_eqb_le (fst p) x) as Heqb.
    time_unfold T_karr_without_key. unfold X.bits in *. time_simpl. nia.
  Qed.

  (** Filtering the source is linear in its public row size. *)
  Lemma T_karr_without_filter_le : forall x r,
    (List.T_filter (karr_without_key x) (T_karr_without_key x) (lhs r) <=
      (X.c_key + 8) * N.of_nat (C.lsize r))%N.
  Proof.
    intros x r.
    assert (Hfilter : (List.T_filter (karr_without_key x) (T_karr_without_key x)
      (lhs r) <= ((X.c_key + 4) * N.of_nat (C.row_key_bits r + 1) + 1) *
        N.of_nat (length (lhs r)) + 1)%N).
    { apply karr_T_filter_members. intros p Hin. apply T_karr_without_key_le.
      now apply karr_row_key_member with (r := r). }
    pose proof (karr_lsize_parts r) as [Hparts [_ Hkeys]]. nia.
  Qed.

  (** The normalizer receives the surviving source terms and one scaled form. *)
  Definition karr_subst_input (x : X.t) (f : lin X.t) (r : lcons X.t)
      : list (X.t * Z) :=
    filter (karr_without_key x) (lhs r) ++ scale_coef (coefficient x (lhs r)) (coef f).

  (** Aggregate substitution never creates more than the two input lists' total length. *)
  Lemma karr_subst_input_length : forall x f r,
    length (karr_subst_input x f r) <= length (lhs r) + length (coef f).
  Proof.
    intros x f r. unfold karr_subst_input, scale_coef.
    rewrite length_app, length_map. apply Nat.add_le_mono_r, filter_length_le.
  Qed.

  (** The substitution list has bounded original keys and product coefficient widths. *)
  Lemma karr_subst_input_sizes : forall x f r,
    Forall (fun p => Pos.size_nat (X.encode (fst p)) <=
      C.row_key_bits r + C.row_key_bits (LCons X.t (coef f) REq (cst f)) /\
      Z.size_nat (snd p) <= length (lhs r) + C.row_bits r +
        C.row_bits (LCons X.t (coef f) REq (cst f))) (karr_subst_input x f r).
  Proof.
    intros x f r. unfold karr_subst_input. apply Forall_app. split.
    - apply Forall_forall. intros p Hin. apply filter_In in Hin as [Hin _].
      pose proof (karr_row_key_member r p Hin).
      pose proof (karr_row_entry_bits r p Hin). split; lia.
    - apply Forall_forall. intros [y z] Hin. unfold scale_coef in Hin.
      apply in_map_iff in Hin as [[u a] [Heq Hin]]. cbn [fst snd] in Heq.
      injection Heq as Heqy Heqz. subst y z.
      pose proof (karr_row_key_member (LCons X.t (coef f) REq (cst f))
        (u, a) Hin) as Hkey.
      pose proof (karr_row_entry_bits (LCons X.t (coef f) REq (cst f))
        (u, a) Hin) as Hbits.
      pose proof (karr_raw_row_coefficient_bits x r) as Hcoefficient.
      pose proof (karr_size_mul (coefficient x (lhs r)) a) as Hmul.
      cbn [fst snd] in *. split; lia.
  Qed.
  (** The query key and both public row sizes form the frozen substitution extent. *)
  Definition karr_subst_extent (x : X.t) (f : lin X.t) (r : lcons X.t) : nat :=
    X.bits x + C.lsize (LCons X.t (coef f) REq (cst f)) + C.lsize r + 1.

  (** Every substitution extent is positive. *)
  Lemma karr_subst_extent_positive : forall x f r, 1 <= karr_subst_extent x f r.
  Proof.
    intros x f r. unfold karr_subst_extent. lia.
  Qed.

  (** The extent bounds all original lengths and widths together. *)
  Lemma karr_subst_extent_inputs : forall x f r,
    X.bits x + length (lhs r) + length (coef f) + C.row_key_bits r +
      C.row_key_bits (LCons X.t (coef f) REq (cst f)) + C.row_bits r +
      C.row_bits (LCons X.t (coef f) REq (cst f)) + 3 <= karr_subst_extent x f r.
  Proof.
    intros x f r. pose proof (karr_lsize_parts r) as [Hr _].
    pose proof (karr_lsize_parts (LCons X.t (coef f) REq (cst f))) as [Hf _].
    change (length (coef f) + C.row_key_bits (LCons X.t (coef f) REq (cst f)) +
      C.row_bits (LCons X.t (coef f) REq (cst f)) + 1 <=
      C.lsize (LCons X.t (coef f) REq (cst f))) in Hf.
    unfold karr_subst_extent. lia.
  Qed.

  (** Raw coefficient lookup fits the square of the frozen extent. *)
  Lemma T_karr_subst_coefficient : forall x f r,
    (T_coefficient x (lhs r) <= 2 * (karr_coefficient_factor + 4) *
      N.of_nat ((karr_subst_extent x f r)^2))%N.
  Proof.
    intros x f r. pose proof (karr_subst_extent_inputs x f r) as Hinputs.
    assert (Hbits : Forall (fun p => Z.size_nat (snd p) <= C.row_bits r) (lhs r)).
    { apply Forall_forall. intros p Hp. now apply karr_row_entry_bits with (r := r). }
    pose proof (T_karr_coefficient_bounded x (lhs r) (C.row_bits r) Hbits) as Htime.
    assert (Hlength : (N.of_nat (length (lhs r) + 1) <=
      1 * N.of_nat (karr_subst_extent x f r))%N) by lia.
    assert (Hwidth : (N.of_nat (X.bits x + 2 * C.row_bits r + length (lhs r) + 1) <=
      2 * N.of_nat (karr_subst_extent x f r))%N) by lia.
    pose proof (karr_clock_product_bound _ _ _ _ _ _ _ Htime Hlength Hwidth) as Hbound.
    rewrite <- karr_nat_square in Hbound.
    replace ((karr_coefficient_factor + 4) * 1 * 2)%N
      with (2 * (karr_coefficient_factor + 4))%N in Hbound by ring.
    exact Hbound.
  Qed.

  (** The scaled form pays one source-size factor and one form-size factor. *)
  Lemma T_karr_subst_scale : forall x f r,
    (T_scale_coef (coefficient x (lhs r)) (coef f) <=
      16 * N.of_nat ((karr_subst_extent x f r)^2))%N.
  Proof.
    intros x f r. set (a := coefficient x (lhs r)).
    set (fr := LCons X.t (coef f) REq (cst f)).
    pose proof (karr_raw_row_coefficient_bits x r) as Ha. fold a in Ha.
    pose proof (karr_lsize_parts r) as [Hr _].
    pose proof (karr_lsize_parts fr) as [_ [Hform _]].
    change ((length (coef f) + 1) * (C.row_bits fr + 1) <= C.lsize fr) in Hform.
    assert (Hbits : Forall (fun p => Z.size_nat (snd p) <= C.row_bits fr) (coef f)).
    { apply Forall_forall. intros p Hin. exact (karr_row_entry_bits fr p Hin). }
    pose proof (T_karr_scale_coef_bounded a (coef f) (C.row_bits fr) Hbits) as Htime.
    replace (16 * N.of_nat ((length (coef f) + 1) * (Z.size_nat a + 1) *
      (C.row_bits fr + 1)))%N with
      (16 * N.of_nat ((length (coef f) + 1) * (C.row_bits fr + 1)) *
        N.of_nat (Z.size_nat a + 1))%N in Htime by (rewrite !Nat2N.inj_mul; ring).
    assert (Hleft : (N.of_nat ((length (coef f) + 1) * (C.row_bits fr + 1)) <=
      1 * N.of_nat (karr_subst_extent x f r))%N).
    { unfold karr_subst_extent. fold fr. lia. }
    assert (Hright : (N.of_nat (Z.size_nat a + 1) <=
      1 * N.of_nat (karr_subst_extent x f r))%N).
    { unfold karr_subst_extent. fold fr. lia. }
    pose proof (karr_clock_product_bound _ _ _ _ _ _ _ Htime Hleft Hright) as Hbound.
    rewrite <- karr_nat_square in Hbound. exact Hbound.
  Qed.

  (** Normalizing the aggregate list fits four multiples of the same square. *)
  Lemma T_karr_subst_normal : forall x f r,
    (T_normalize_coef (karr_subst_input x f r) <=
      4 * karr_raw_normal_factor * N.of_nat ((karr_subst_extent x f r)^2))%N.
  Proof.
    intros x f r. set (fr := LCons X.t (coef f) REq (cst f)).
    pose proof (karr_subst_extent_inputs x f r) as Hinputs. fold fr in Hinputs.
    pose proof (karr_subst_input_length x f r) as Hlength.
    pose proof (T_karr_normal_raw (karr_subst_input x f r)
      (C.row_key_bits r + C.row_key_bits fr)
      (length (lhs r) + C.row_bits r + C.row_bits fr)
      (karr_subst_input_sizes x f r)) as Htime.
    assert (Hleft : (N.of_nat (length (karr_subst_input x f r) + 1) <=
      1 * N.of_nat (karr_subst_extent x f r))%N) by lia.
    assert (Hright : (N.of_nat (C.row_key_bits r + C.row_key_bits fr +
      2 * (length (lhs r) + C.row_bits r + C.row_bits fr) +
      2 * length (karr_subst_input x f r) + 1) <=
      4 * N.of_nat (karr_subst_extent x f r))%N) by lia.
    pose proof (karr_clock_product_bound _ _ _ _ _ _ _ Htime Hleft Hright) as Hbound.
    rewrite <- karr_nat_square in Hbound.
    replace (karr_raw_normal_factor * 1 * 4)%N
      with (4 * karr_raw_normal_factor)%N in Hbound by ring. exact Hbound.
  Qed.

  (** Source filtering also fits the shared square envelope. *)
  Lemma T_karr_subst_filter : forall x f r,
    (List.T_filter (karr_without_key x) (T_karr_without_key x) (lhs r) <=
      (X.c_key + 8) * N.of_nat ((karr_subst_extent x f r)^2))%N.
  Proof.
    intros x f r. pose proof (T_karr_without_filter_le x r) as Htime.
    pose proof (karr_nat_square_ge _ (karr_subst_extent_positive x f r)) as Hsquare.
    eapply N.le_trans; [exact Htime|]. apply N.mul_le_mono_l.
    unfold karr_subst_extent in *. lia.
  Qed.

  (** Appending the aggregate form traverses only the surviving source list. *)
  Lemma T_karr_subst_app : forall x f r,
    (Datatypes.T_app (filter (karr_without_key x) (lhs r))
      (scale_coef (coefficient x (lhs r)) (coef f)) <=
      N.of_nat ((karr_subst_extent x f r)^2))%N.
  Proof.
    intros x f r. pose proof (karr_subst_extent_inputs x f r) as Hinputs.
    pose proof (karr_nat_square_ge _ (karr_subst_extent_positive x f r)) as Hsquare.
    pose proof (filter_length_le (karr_without_key x) (lhs r)) as Hlength.
    pose proof (Datatypes.T_app_le (filter (karr_without_key x) (lhs r))
      (scale_coef (coefficient x (lhs r)) (coef f))) as Htime. lia.
  Qed.

  (** The constant adjustment has one product and one bounded subtraction. *)
  Lemma T_karr_subst_arithmetic : forall x f r,
    (Z.T_mul (coefficient x (lhs r)) (cst f) <=
      8 * N.of_nat ((karr_subst_extent x f r)^2))%N /\
    (Z.T_sub (rhs r) (coefficient x (lhs r) * cst f) <=
      12 * N.of_nat ((karr_subst_extent x f r)^2))%N.
  Proof.
    intros x f r. set (a := coefficient x (lhs r)).
    pose proof (karr_subst_extent_inputs x f r) as Hinputs.
    pose proof (karr_raw_row_coefficient_bits x r) as Ha. fold a in Ha.
    pose proof (karr_row_rhs_bits r) as Hr.
    pose proof (karr_row_rhs_bits (LCons X.t (coef f) REq (cst f))) as Hf.
    change (Z.size_nat (cst f) <= C.row_bits (LCons X.t (coef f) REq (cst f))) in Hf.
    pose proof (karr_T_Z_mul_bilinear a (cst f)) as Hmul.
    assert (Hleft : (N.of_nat (Z.size_nat a + 1) <=
      1 * N.of_nat (karr_subst_extent x f r))%N) by lia.
    assert (Hright : (N.of_nat (Z.size_nat (cst f) + 1) <=
      1 * N.of_nat (karr_subst_extent x f r))%N) by lia.
    pose proof (karr_clock_product_bound _ _ _ _ _ _ _ Hmul Hleft Hright) as Hbound.
    rewrite <- karr_nat_square in Hbound. split; [exact Hbound|].
    pose proof (Z.T_sub_le (rhs r) (a * cst f)) as Hsub.
    pose proof (karr_size_mul a (cst f)) as Hproduct.
    pose proof (karr_nat_square_ge _ (karr_subst_extent_positive x f r)) as Hsquare.
    assert (Hlinear : (Z.T_sub (rhs r) (a * cst f) <=
      12 * N.of_nat (karr_subst_extent x f r))%N) by lia.
    eapply N.le_trans; [exact Hlinear|]. now apply N.mul_le_mono_l.
  Qed.

  (** The shared constant covers all traversals and binary arithmetic in substitution. *)
  Definition karr_subst_factor : N :=
    (8 * karr_raw_normal_factor + 4 * karr_coefficient_factor + 8 * X.c_key + 192)%N.

  (** Aggregate substitution satisfies the frozen square bound on arbitrary raw rows. *)
  Lemma T_karr_subst_bounded : forall x f r,
    (T_subst x f r <= karr_subst_factor * N.of_nat
      ((X.bits x + C.lsize (LCons X.t (coef f) REq (cst f)) + C.lsize r + 1)^2))%N.
  Proof.
    intros x f r. set (a := coefficient x (lhs r)).
    set (mass := N.of_nat ((karr_subst_extent x f r)^2)).
    pose proof (T_karr_subst_coefficient x f r) as Hcoefficient.
    pose proof (T_karr_subst_scale x f r) as Hscale.
    pose proof (T_karr_subst_normal x f r) as Hnormal.
    pose proof (T_karr_subst_filter x f r) as Hfilter.
    pose proof (T_karr_subst_app x f r) as Happ.
    destruct (T_karr_subst_arithmetic x f r) as [Hmul Hsub].
    fold mass in Hcoefficient, Hscale, Hnormal, Hfilter, Happ, Hmul, Hsub.
    fold a in Hscale, Happ, Hmul, Hsub.
    assert (Hmass : (1 <= mass)%N).
    { unfold mass. pose proof (karr_subst_extent_positive x f r) as Hpositive.
      pose proof (karr_nat_square_ge _ Hpositive). lia. }
    change (T_subst x f r <= karr_subst_factor * mass)%N.
    time_unfold T_subst. time_unfold T_normalize_row.
    change (fun p => negb (X.eqb (fst p) x)) with (karr_without_key x).
    fold a. fold (karr_subst_input x f r). time_simpl.
    lazymatch goal with
    | |- context [List.T_filter (karr_without_key x) ?Tf (lhs r)] =>
      change Tf with (T_karr_without_key x)
    end.
    change (filter (karr_without_key x) (lhs r) ++ scale_coef a (coef f))
      with (karr_subst_input x f r).
    cbn [lhs]. unfold karr_subst_factor.
    clear -Hcoefficient Hscale Hnormal Hfilter Happ Hmul Hsub Hmass.
    clearbody mass. nia.
  Qed.

  (** Every occurrence count lies below the next power of two above its logarithm. *)
  Lemma karr_log_upper : forall count, count < 2 ^ (Nat.log2 count + 1).
  Proof.
    intros [|count]; [change (0 < 2); lia|].
    pose proof (Nat.log2_spec (S count) (Nat.lt_0_succ count)) as [_ Hupper].
    now replace (Nat.log2 (S count) + 1) with (S (Nat.log2 (S count))) by lia.
  Qed.

  (** A sum of bounded magnitudes needs only the logarithm of their count. *)
  Lemma karr_count_magnitude_bits : forall z count bits,
    karr_magnitude z <= count * 2 ^ bits ->
    Z.size_nat z <= bits + Nat.log2 count + 1.
  Proof.
    intros z count bits Hmagnitude. apply karr_size_least.
    replace (bits + Nat.log2 count + 1) with (bits + (Nat.log2 count + 1)) by lia.
    rewrite Nat.pow_add_r.
    pose proof (karr_log_upper count) as Hcount.
    assert (Hpositive : 0 < 2 ^ bits).
    { pose proof (Nat.pow_nonzero 2 bits ltac:(lia)). lia. }
    nia.
  Qed.

  (** A magnitude budget bounds every coefficient currently stored in the trie. *)
  Definition karr_accum_magnitude (m : ptrie (X.t * Z)) (bound : nat) : Prop :=
    forall key p, PTrieCode.get key m = Some p -> karr_magnitude (snd p) <= bound.

  (** Missing keys contribute zero to the accumulator budget. *)
  Lemma karr_previous_magnitude : forall m bound x,
    karr_accum_magnitude m bound -> karr_magnitude (karr_previous m x) <= bound.
  Proof.
    intros m bound x Hmagnitude. unfold karr_previous.
    destruct (PTrieCode.get (X.encode x) m) as [p|] eqn:Hget.
    - exact (Hmagnitude _ _ Hget).
    - change (0 <= bound). lia.
  Qed.

  (** One insertion adds at most the next raw coefficient's magnitude budget. *)
  Lemma karr_add_term_magnitude : forall m p bound bits,
    karr_accum_magnitude m bound -> Z.size_nat (snd p) <= bits ->
    karr_accum_magnitude (add_term m p) (bound + 2 ^ bits).
  Proof.
    intros m p bound bits Hmagnitude Hbits key q Hget.
    pose proof (karr_magnitude_upper (snd p)) as Hnew.
    assert (Hpower : 2 ^ Z.size_nat (snd p) <= 2 ^ bits).
    { apply Nat.pow_le_mono_r; lia. }
    unfold add_term in Hget.
    destruct (PTrieCode.get (X.encode (fst p)) m) as [old|] eqn:Hold;
      destruct (Pos.eq_dec key (X.encode (fst p))) as [Hequal|Hother].
    - subst key. rewrite PTrie.get_set_same in Hget. injection Hget as Hequal. subst q.
      cbn [snd]. pose proof (karr_magnitude_add (snd old) (snd p)) as Hadd.
      pose proof (Hmagnitude _ _ Hold). lia.
    - rewrite PTrie.get_set_other in Hget by exact Hother.
      specialize (Hmagnitude _ _ Hget). lia.
    - subst key. rewrite PTrie.get_set_same in Hget. injection Hget as Hequal. subst q.
      lia.
    - rewrite PTrie.get_set_other in Hget by exact Hother.
      specialize (Hmagnitude _ _ Hget). lia.
  Qed.

  (** Folding a raw list spends one magnitude budget for every occurrence. *)
  Lemma karr_accum_magnitude_fold : forall xs m bound bits,
    Forall (fun p => Z.size_nat (snd p) <= bits) xs ->
    karr_accum_magnitude m bound ->
    karr_accum_magnitude (fold_left add_term xs m) (bound + length xs * 2 ^ bits).
  Proof.
    intro xs. induction xs as [|p xs IH]; intros m bound bits Hsizes Hmagnitude;
      cbn [fold_left length].
    - now rewrite Nat.add_0_r.
    - inversion Hsizes as [|q qs Hp Htail]; subst q qs.
      replace (bound + S (length xs) * 2 ^ bits) with
        ((bound + 2 ^ bits) + length xs * 2 ^ bits) by nia.
      apply IH; [exact Htail|]. now apply karr_add_term_magnitude.
  Qed.

  (** Every retained normalized coefficient is read from the completed accumulator. *)
  Lemma karr_normal_coef_lookup : forall xs p, In p (normalize_coef xs) ->
    exists key, PTrieCode.get key (fold_left add_term xs PTrieCode.empty) = Some p.
  Proof.
    intros xs p Hin. unfold normalize_coef in Hin. apply filter_In in Hin as [Hin _].
    rewrite karr_values_elements in Hin.
    apply in_map_iff in Hin as [[key q] [Hsame Hin]]. cbn [snd] in Hsame. subst q.
    exists key. now apply (proj1 (PTrie.elements_spec _ _ _ _)).
  Qed.

  (** Normalized coefficients have logarithmic growth in the raw occurrence count. *)
  Lemma karr_normal_coef_log_bits : forall xs bits,
    Forall (fun p => Z.size_nat (snd p) <= bits) xs ->
    Forall (fun p => Z.size_nat (snd p) <= bits + Nat.log2 (length xs) + 1)
      (normalize_coef xs).
  Proof.
    intros xs bits Hsizes.
    assert (Hempty : karr_accum_magnitude PTrieCode.empty 0).
    { intros key p Hget. rewrite PTrie.get_empty in Hget. discriminate. }
    pose proof (karr_accum_magnitude_fold xs PTrieCode.empty 0 bits Hsizes Hempty)
      as Hmagnitude.
    apply Forall_forall. intros p Hin. apply karr_count_magnitude_bits.
    destruct (karr_normal_coef_lookup _ _ Hin) as [key Hget].
    exact (Hmagnitude _ _ Hget).
  Qed.

  (** A bounded seed and bounded entries give the same bound on a maximum fold. *)
  Lemma karr_max_bound : forall A (f : A -> nat) seed xs bound,
    seed <= bound -> Forall (fun x => f x <= bound) xs ->
    fold_right Nat.max seed (map f xs) <= bound.
  Proof.
    intros A f seed xs bound Hseed Hentries. induction Hentries;
      cbn [map fold_right]; lia.
  Qed.

  (** A prepared row gains only a logarithmic coefficient-width allowance. *)
  Lemma karr_normal_row_log_bits : forall r,
    C.row_bits (normalize_row r) <= C.row_bits r + Nat.log2 (length (lhs r)) + 1.
  Proof.
    intro r. unfold C.row_bits at 1. cbn [normalize_row lhs rhs].
    apply karr_max_bound.
    - pose proof (karr_row_rhs_bits r). lia.
    - apply karr_normal_coef_log_bits. apply Forall_forall. intros p Hin.
      exact (karr_row_entry_bits r p Hin).
  Qed.

  (** The fold clock uses one width budget for every prefix of the complete input. *)
  Lemma T_karr_accum_log : forall xs m keys bits used total,
    Forall (fun p => Pos.size_nat (X.encode (fst p)) <= keys /\
      Z.size_nat (snd p) <= bits) xs ->
    karr_accum_magnitude m (used * 2 ^ bits) -> used + length xs <= total ->
    (List.T_fold_left add_term T_add_term xs m <=
      (karr_add_factor + 1) * N.of_nat (length xs) *
        N.of_nat (keys + 2 * bits + Nat.log2 total + 2) + 1)%N.
  Proof.
    intro xs. induction xs as [|p xs IH]; intros m keys bits used total Hsizes Hmagnitude Hcount.
    - time_unfold List.T_fold_left. cbn [length]. nia.
    - inversion Hsizes as [|q qs [Hkey Hbits] Htail]; subst q qs.
      assert (Hprevious : Z.size_nat (karr_previous m (fst p)) <=
        bits + Nat.log2 total + 1).
      { apply karr_count_magnitude_bits.
        pose proof (karr_previous_magnitude m (used * 2 ^ bits) (fst p) Hmagnitude).
        cbn [length] in Hcount. nia. }
      assert (Hnext : karr_accum_magnitude (add_term m p) ((used + 1) * 2 ^ bits)).
      { replace ((used + 1) * 2 ^ bits) with (used * 2 ^ bits + 2 ^ bits) by nia.
        now apply karr_add_term_magnitude. }
      specialize (IH (add_term m p) keys bits (used + 1) total Htail Hnext
        ltac:(cbn [length] in Hcount; lia)).
      pose proof (T_karr_add_term_bounded m p keys bits
        (bits + Nat.log2 total + 1) Hkey Hbits Hprevious) as Hhead.
      time_unfold List.T_fold_left. cbn [length]. time_simpl.
      rewrite !Nat2N.inj_add, !Nat2N.inj_mul in *. cbn [N.of_nat] in *. nia.
  Qed.

  (** Raw normalization charges each occurrence at the logarithmic merged width. *)
  Lemma T_karr_normal_log : forall xs keys bits,
    Forall (fun p => Pos.size_nat (X.encode (fst p)) <= keys /\
      Z.size_nat (snd p) <= bits) xs ->
    (T_normalize_coef xs <= karr_raw_normal_factor * N.of_nat (length xs + 1) *
      N.of_nat (keys + bits + Nat.log2 (length xs) + 1))%N.
  Proof.
    intros xs keys bits Hsizes.
    assert (Hempty : karr_accum_magnitude PTrieCode.empty (0 * 2 ^ bits)).
    { intros key p Hget. rewrite PTrie.get_empty in Hget. discriminate. }
    pose proof (T_karr_accum_log xs PTrieCode.empty keys bits 0 (length xs)
      Hsizes Hempty ltac:(lia)) as Haccum.
    set (tr := fold_left add_term xs PTrieCode.empty).
    assert (Hkeys : Forall (fun p => Pos.size_nat (X.encode (fst p)) <= keys) xs).
    { eapply Forall_impl; [|exact Hsizes]. intros p [Hp _]. exact Hp. }
    pose proof (karr_accum_nodes xs PTrieCode.empty keys Hkeys) as Hnodes.
    change (PTrie.nodes tr <= length xs * keys) in Hnodes.
    pose proof (T_karr_values_bounded (X.t * Z) tr) as Hvalues.
    pose proof (karr_values_length (X.t * Z) tr) as Hlength.
    pose proof (karr_T_filter_members (X.t * Z) karr_nonzero T_karr_nonzero 6
      (karr_values tr) (fun p _ => T_karr_nonzero_bounded p)) as Hfilter.
    time_unfold T_normalize_coef. fold tr.
    change (fun p : X.t * Z => negb (Z.eqb (snd p) 0)) with karr_nonzero.
    time_simpl.
    change (fun (m : ptrie (X.t * Z)) (p : X.t * Z) => T_add_term m p) with T_add_term.
    lazymatch goal with
    | |- context [List.T_filter karr_nonzero ?Tf (karr_values tr)] =>
      change Tf with T_karr_nonzero
    end.
    unfold karr_raw_normal_factor.
    rewrite !Nat2N.inj_add, !Nat2N.inj_mul in *. cbn [N.of_nat] in *. nia.
  Qed.
  (** An inserted binding uses the new key or an already present address. *)
  Lemma karr_add_key_origin : forall m p key q,
    PTrieCode.get key (add_term m p) = Some q ->
    key = X.encode (fst p) \/ exists old, PTrieCode.get key m = Some old.
  Proof.
    intros m p key q Hget. destruct (Pos.eq_dec key (X.encode (fst p))) as [Heq|Hother].
    - now left.
    - right. unfold add_term in Hget.
      destruct (PTrieCode.get (X.encode (fst p)) m);
        rewrite PTrie.get_set_other in Hget by exact Hother;
        exists q; exact Hget.
  Qed.

  (** Every accumulator address comes from a scanned occurrence or its initial table. *)
  Lemma karr_fold_key_origin : forall xs m key q,
    PTrieCode.get key (fold_left add_term xs m) = Some q ->
    In key (map (fun p => X.encode (fst p)) xs) \/
      exists old, PTrieCode.get key m = Some old.
  Proof.
    intro xs. induction xs as [|p xs IH]; intros m key q Hget; cbn [fold_left] in Hget.
    - right. now exists q.
    - destruct (IH _ _ _ Hget) as [Hin|[old Hold]].
      + left. now right.
      + destruct (karr_add_key_origin m p key old Hold) as [Heq|Hbefore].
        * left. left. symmetry. exact Heq.
        * now right.
  Qed.

  (** Every key enumerated from a fresh accumulator occurs in the raw source. *)
  Lemma karr_accum_keys : forall xs p,
    In p (karr_values (fold_left add_term xs PTrieCode.empty)) ->
    In (fst p) (map fst xs).
  Proof.
    intros xs p Hin. rewrite karr_values_elements in Hin.
    apply in_map_iff in Hin as [[key q] [Hsame Hin]]. cbn [snd] in Hsame. subst q.
    apply (proj1 (PTrie.elements_spec _ _ _ _)) in Hin.
    pose proof (normalize_fold_wf xs PTrieCode.empty normalization_empty key p Hin) as Haddress.
    destruct (karr_fold_key_origin _ _ _ _ Hin) as [Hsource|[q Hempty]].
    - apply in_map_iff in Hsource as [r [Hkey Hr]].
      apply in_map_iff. exists r. split; [|exact Hr].
      apply X.encode_inj. now rewrite Hkey, Haddress.
    - rewrite PTrie.get_empty in Hempty. discriminate.
  Qed.

  (** Merging and deleting coefficients never introduces a new raw key. *)
  Lemma karr_normal_coef_keys : forall xs p,
    In p (normalize_coef xs) -> In (fst p) (map fst xs).
  Proof.
    intros xs p Hin. unfold normalize_coef in Hin. apply filter_In in Hin as [Hin _].
    now apply karr_accum_keys.
  Qed.

  (** Every executable coordinate belongs to a source row's raw key list. *)
  Lemma karr_variables_support : forall P x,
    In x (variables P) -> exists r, In r P /\ In x (map fst (lhs r)).
  Proof.
    intros P x Hin. unfold variables in Hin.
    apply in_map_iff in Hin as [p [Hsame Hin]]. subst x.
    apply karr_accum_keys in Hin. apply in_map_iff in Hin as [q [Hsame Hin]].
    apply in_flat_map in Hin as [r [Hr Hq]]. exists r. split; [exact Hr|].
    apply in_map_iff. exists q. split; assumption.
  Qed.

  (** The declared set insertion retains its prior members and the inserted variable. *)
  Lemma karr_var_insert_contains : forall acc x y,
    In y acc \/ y = x ->
    In y (if existsb (X.eqb x) acc then acc else x :: acc).
  Proof.
    intros acc x y Hin. destruct (existsb (X.eqb x) acc) eqn:Hpresent.
    - destruct Hin as [Hin|Heq]; [exact Hin|]. subst y.
      apply existsb_exists in Hpresent as [z [Hz Heq]].
      destruct (X.eqb_spec x z) as [Hequal|Hneq]; [now subst z|discriminate].
    - destruct Hin as [Hin|Heq]; [right; exact Hin|left; congruence].
  Qed.

  (** The declared variable fold contains every scanned variable. *)
  Lemma karr_vars_fold_contains : forall xs acc x,
    In x acc \/ In x xs ->
    In x (fold_left (fun acc y => if existsb (X.eqb y) acc then acc else y :: acc) xs acc).
  Proof.
    intro xs. induction xs as [|y xs IH]; intros acc x Hin; cbn [fold_left].
    - destruct Hin as [Hin|Hin]; [exact Hin|contradiction].
    - apply IH. destruct Hin as [Hin|[Heq|Hin]].
      + left. apply karr_var_insert_contains. now left.
      + left. apply karr_var_insert_contains. right. congruence.
      + now right.
  Qed.

  (** The public source dimension contains every raw row variable. *)
  Lemma karr_vars_of_contains : forall P r x,
    In r P -> In x (map fst (lhs r)) -> In x (vars_of P).
  Proof.
    intros P r x Hr Hx. unfold vars_of. apply karr_vars_fold_contains. right.
    apply in_flat_map. exists r. auto.
  Qed.

  (** Unique executable coordinates fit the dimension declared by the signature. *)
  Lemma karr_variables_count : forall P, length (variables P) <= length (vars_of P).
  Proof.
    intro P. apply NoDup_incl_length; [apply variables_nodup|].
    intros x Hx. destruct (karr_variables_support P x Hx) as [r [Hr Hterm]].
    now apply karr_vars_of_contains with (r := r).
  Qed.

  (** A normalized source row has at most one term per original source variable. *)
  Lemma karr_normal_row_dimension : forall P r, In r P ->
    length (lhs (normalize_row r)) <= length (vars_of P).
  Proof.
    intros P r Hr. cbn [normalize_row lhs]. rewrite <- (length_map fst (normalize_coef (lhs r))).
    apply NoDup_incl_length; [apply normalize_coef_nodup|].
    intros x Hin. apply in_map_iff in Hin as [p [Hsame Hp]]. subst x.
    apply karr_vars_of_contains with (r := r); [exact Hr|].
    now apply karr_normal_coef_keys.
  Qed.

  (** Preparing a row never increases its maximum encoded-key width. *)
  Lemma karr_normal_row_key_bits : forall r,
    C.row_key_bits (normalize_row r) <= C.row_key_bits r.
  Proof.
    intro r. unfold C.row_key_bits at 1. cbn [normalize_row lhs].
    apply karr_max_bound; [lia|]. apply Forall_forall. intros p Hin.
    apply karr_normal_coef_keys in Hin.
    apply in_map_iff in Hin as [q [Hsame Hq]]. rewrite <- Hsame.
    exact (karr_row_key_member r q Hq).
  Qed.

  (** One row's raw occurrences are included in the complete source occurrence count. *)
  Lemma karr_terms_member : forall P r, In r P -> length (lhs r) <= terms (Reached P).
  Proof.
    intro P. induction P as [|p P IH]; intros r Hin; [contradiction|].
    change (length (lhs r) <= length (lhs p) + terms (Reached P)).
    destruct Hin as [Heq|Hin]; [subst r; lia|]. pose proof (IH r Hin). lia.
  Qed.

  (** Every prepared source row fits the signature's logarithmic raw width. *)
  Lemma karr_normal_source_width : forall P,
    Forall (fun r => C.row_key_bits r + C.row_bits r <= nell (Reached P))
      (map normalize_row P).
  Proof.
    intros P. apply Forall_map, Forall_forall. intros r Hr.
    pose proof (karr_normal_row_key_bits r) as Hkeys.
    pose proof (karr_normal_row_log_bits r) as Hbits.
    pose proof (karr_max_member _ C.row_key_bits 0 P r Hr) as Hrawkeys.
    pose proof (karr_max_member _ C.row_bits 0 P r Hr) as Hrawbits.
    pose proof (Nat.log2_le_mono _ _ (karr_terms_member P r Hr)) as Hlog.
    unfold nell, ell. cbn [rows_of]. lia.
  Qed.

  (** A common row length bounds the total number of raw occurrences. *)
  Lemma karr_terms_rows_bound : forall P dim,
    Forall (fun r => length (lhs r) <= dim) P ->
    terms (Reached P) <= length P * dim.
  Proof.
    intros P dim Hrows. induction Hrows as [|r P Hrow Htail IH].
    - cbn [terms rows_of map fold_right length]. lia.
    - change (length (lhs r) + terms (Reached P) <= S (length P) * dim).
      nia.
  Qed.

  (** Normal source rows give a quadratic bound on their raw occurrences. *)
  Lemma karr_normal_terms_bound : forall P,
    normal P -> terms (Reached P) <= length P * length (vars_of P).
  Proof.
    intros P Hnormal. apply karr_terms_rows_bound.
    apply Forall_forall. intros r Hr.
    rewrite <- (length_map fst (lhs r)).
    apply NoDup_incl_length.
    - exact (proj1 (Forall_forall _ _) Hnormal r Hr).
    - intros x Hx. eapply karr_vars_of_contains; eassumption.
  Qed.

  (** A quadratic occurrence count contributes only two dimension logarithms. *)
  Lemma karr_log_square_bound : forall count dim,
    count <= dim * dim ->
    Nat.log2 count <= 2 * (Nat.log2 dim + 1).
  Proof.
    intros count dim Hcount.
    pose proof (karr_log_upper dim) as Hbase.
    assert (Hsquare : dim ^ 2 < (2 ^ (Nat.log2 dim + 1)) ^ 2).
    { apply Nat.pow_lt_mono_l; lia. }
    assert (Hpower : count < (2 ^ (Nat.log2 dim + 1)) ^ 2).
    { rewrite Nat.pow_2_r in Hsquare. nia. }
    rewrite <- Nat.pow_mul_r in Hpower.
    pose proof (Nat.log2_le_mono count (2 ^ ((Nat.log2 dim + 1) * 2))
      (Nat.lt_le_incl _ _ Hpower)) as Hlog.
    rewrite Nat.log2_pow2 in Hlog by lia. lia.
  Qed.

  (** Normal input gives a logarithmic raw occurrence width in its dimension. *)
  Lemma karr_normal_terms_log : forall P,
    normal P -> Nat.log2 (terms (Reached P)) <=
      2 * (Nat.log2 (n (Reached P) + 1) + 1).
  Proof.
    intros P Hnormal.
    pose proof (karr_normal_terms_bound P Hnormal) as Hterms.
    assert (Hsquare : terms (Reached P) <= n (Reached P) * n (Reached P)).
    { unfold n. cbn [rows_of]. nia. }
    pose proof (karr_log_square_bound _ _ Hsquare) as Hlog.
    pose proof (Nat.log2_le_mono (n (Reached P)) (n (Reached P) + 1)
      ltac:(lia)) as Hmono. lia.
  Qed.

  (** Normal source rows fit the public dimension and maximum input widths. *)
  Lemma karr_normal_source_envelope : forall P,
    normal P -> Forall (fun r => length (lhs r) <= n (Reached P) /\
      C.row_key_bits r <= ell (Reached P) /\
      C.row_bits r <= ell (Reached P)) P.
  Proof.
    intros P Hnormal. apply Forall_forall. intros r Hr.
    assert (Hterms : length (lhs r) <= length (vars_of P)).
    { rewrite <- (length_map fst (lhs r)).
      apply NoDup_incl_length.
      - exact (proj1 (Forall_forall _ _) Hnormal r Hr).
      - intros x Hx. eapply karr_vars_of_contains; eassumption. }
    pose proof (karr_max_member _ C.row_key_bits 0 P r Hr) as Hkeys.
    pose proof (karr_max_member _ C.row_bits 0 P r Hr) as Hbits.
    unfold n, ell. cbn [rows_of]. repeat split; lia.
  Qed.

  (** A coefficient in a row with unique keys never adds distinct occurrences together. *)
  Lemma karr_coefficient_normal_bits : forall xs x bits,
    NoDup (map fst xs) -> Forall (fun p => Z.size_nat (snd p) <= bits) xs ->
    Z.size_nat (coefficient x xs) <= bits.
  Proof.
    intro xs. induction xs as [|[y a] xs IH]; intros x bits Hunique Hsizes;
      [change (0 <= bits); lia|].
    inversion Hunique as [|key keys Hnot Htail]; subst key keys.
    inversion Hsizes as [|p ps Hhead Hsizes']; subst p ps.
    rewrite coefficient_cons. destruct (X.eqb_spec x y) as [Hequal|Hother].
    - subst x. rewrite (coefficient_absent y xs Hnot), Z.add_0_r. exact Hhead.
    - rewrite Z.add_0_l. now apply IH.
  Qed.


  (** A one-column matrix carries bounded coordinate and multiplier vectors. *)
  Definition karr_row_envelope (dim mlen bits : nat) (r : karr_row) : Prop :=
    length (kcoeff r) <= dim /\
    Forall (fun z => Z.size_nat z <= bits) (kcoeff r) /\
    Z.size_nat (kright r) <= bits /\
    length (kweight r) <= mlen /\
    Forall (fun z => Z.size_nat z <= bits) (kweight r) /\
    Z.size_nat (kscale r) <= bits.

  (** Larger dimensions and bit limits preserve a row envelope. *)
  Lemma karr_row_envelope_resize : forall dim mlen bits dim' mlen' bits' r,
    dim <= dim' -> mlen <= mlen' -> bits <= bits' ->
    karr_row_envelope dim mlen bits r ->
    karr_row_envelope dim' mlen' bits' r.
  Proof.
    intros dim mlen bits dim' mlen' bits' r Hdim Hmlen Hbits
      [Hcoeff [Hcoeff_bits [Hrhs [Hweight [Hweight_bits Hscale]]]]].
    unfold karr_row_envelope. repeat split.
    - lia.
    - eapply Forall_impl; [|exact Hcoeff_bits]. intros z Hz; cbn beta in Hz; lia.
    - lia.
    - lia.
    - eapply Forall_impl; [|exact Hweight_bits]. intros z Hz; cbn beta in Hz; lia.
    - lia.
  Qed.

  (** A bounded augmented vector gives the componentwise row envelope. *)
  Lemma karr_row_envelope_entries : forall dim mlen bits r,
    length (kcoeff r) <= dim -> length (kweight r) <= mlen ->
    Forall (fun z => Z.size_nat z <= bits) (karr_row_entries r) ->
    karr_row_envelope dim mlen bits r.
  Proof.
    intros dim mlen bits r Hcoeff_length Hweight_length Hentries.
    unfold karr_row_entries in Hentries.
    apply Forall_app in Hentries as [Hcoeff Hright_tail].
    apply Forall_cons_iff in Hright_tail as [Hright Hweight_tail].
    apply Forall_app in Hweight_tail as [Hweight Hscale_tail].
    apply Forall_cons_iff in Hscale_tail as [Hscale _].
    unfold karr_row_envelope. repeat split; assumption.
  Qed.

  (** The maintained minor law supplies one envelope for every live row. *)
  Lemma karr_run_state_envelope : forall width cols original previous
      pivot_rows pivot_columns columns labels rows budget bits,
    karr_run_state width cols original previous pivot_rows pivot_columns
      columns labels rows ->
    length columns <= budget ->
    (forall z, In z (karr_signed_minors width original) -> Z.size_nat z <= bits) ->
    Forall (karr_row_envelope budget budget bits) rows.
  Proof.
    intros width cols original previous pivot_rows pivot_columns columns labels
      rows budget bits Hstate Hbudget Hbits.
    pose proof (karr_run_state_bits width cols original previous pivot_rows
      pivot_columns columns labels rows bits Hstate Hbits) as Hrows_bits.
    unfold karr_run_state in Hstate.
    destruct Hstate as [_ [_ [_ [Hcoeff [Hentries [Hcols _]]]]]].
    apply Forall_forall. intros row Hrow.
    pose proof (proj1 (Forall_forall _ _) Hcoeff row Hrow) as Hcoeff_length.
    pose proof (proj1 (Forall_forall _ _) Hentries row Hrow) as Hentries_length.
    pose proof (proj1 (Forall_forall _ _) Hrows_bits row Hrow) as Hrow_bits.
    cbn beta in Hcoeff_length, Hentries_length, Hrow_bits.
    apply karr_row_envelope_entries.
    - lia.
    - unfold karr_row_entries in Hentries_length.
      cbn [length] in Hentries_length.
      rewrite !length_app in Hentries_length. cbn [length] in Hentries_length.
      rewrite length_app in Hentries_length. cbn [length] in Hentries_length. lia.
    - exact Hrow_bits.
  Qed.

  (** Certificate traversal fits a row count times the largest per-row charge. *)
  Lemma karr_csize_envelope : forall P ms dim keys bits mbits,
    Forall (fun r => length (lhs r) <= dim /\
      C.row_key_bits r <= keys /\ C.row_bits r <= bits) P ->
    Forall (fun m => Z.size_nat m <= mbits) ms ->
    C.csize P ms <= (length P + length ms + 1) * (dim + 1) *
      (keys + (mbits + 1) * (bits + 1) + 1).
  Proof.
    intro P. induction P as [|p P IH]; intros [|m ms] dim keys bits mbits Hrows Hmult;
      cbn [C.csize length]; try nia.
    inversion Hrows as [|? ? [Hlen [Hkey Hbits]] Htail]; subst.
    inversion Hmult as [|? ? Hm Hmult_tail]; subst.
    pose proof (IH ms dim keys bits mbits Htail Hmult_tail) as Hrest.
    assert (Hterm : (length (lhs p) + 1) *
        (C.row_key_bits p + (Z.size_nat m + 1) * (C.row_bits p + 1)) <=
        (dim + 1) * (keys + (mbits + 1) * (bits + 1) + 1)).
    { apply Nat.mul_le_mono; [lia|].
      assert (Hprod : (Z.size_nat m + 1) * (C.row_bits p + 1) <=
        (mbits + 1) * (bits + 1)) by (apply Nat.mul_le_mono; lia).
      lia. }
    nia.
  Qed.

  (** Certificate bit width is bounded by multiplier and source-row widths. *)
  Lemma karr_cbits_envelope : forall P ms bits mbits,
    Forall (fun r => C.row_bits r <= bits) P ->
    Forall (fun m => Z.size_nat m <= mbits) ms ->
    C.cbits P ms <= mbits + bits + Nat.log2 (length P) + 1.
  Proof.
    intros P ms bits mbits Hrows Hmult.
    unfold C.cbits.
    assert (Hmax : fold_right Nat.max 0
        (map (fun pm => Z.size_nat (snd pm) + C.row_bits (fst pm))
          (List.combine P ms)) <= mbits + bits).
    { apply karr_max_bound; [lia|].
      apply Forall_forall. intros [row m] Hin.
      pose proof (in_combine_l _ _ _ _ Hin) as Hrow.
      pose proof (in_combine_r _ _ _ _ Hin) as Hm.
      pose proof (proj1 (Forall_forall _ _) Hrows row Hrow) as Hbits.
      pose proof (proj1 (Forall_forall _ _) Hmult m Hm) as Hmbits.
      cbn in Hbits, Hmbits.
      cbn [fst snd]. lia. }
    lia.
  Qed.

  (** A bounded conclusion row has a bounded checker size. *)
  Lemma karr_lsize_envelope : forall row dim keys bits,
    length (lhs row) <= dim -> C.row_key_bits row <= keys ->
    C.row_bits row <= bits ->
    C.lsize row <= (dim + 1) * (keys + bits + 1).
  Proof.
    intros row dim keys bits Hlength Hkeys Hbits.
    unfold C.lsize. apply Nat.mul_le_mono; lia.
  Qed.

  (** Increasing the arithmetic budget preserves a row envelope. *)
  Lemma karr_row_envelope_mono : forall dim mlen bits bits' r,
    bits <= bits' -> karr_row_envelope dim mlen bits r ->
    karr_row_envelope dim mlen bits' r.
  Proof.
    intros dim mlen bits bits' r Hle [Hdim [Hcoeff [Hrhs [Hmlen [Hmult Hscale]]]]].
    split; [exact Hdim|]. split.
    - eapply Forall_impl; [|exact Hcoeff]. intros z Hz. exact (Nat.le_trans _ _ _ Hz Hle).
    - split; [lia|]. split; [exact Hmlen|]. split.
      + eapply Forall_impl; [|exact Hmult]. intros z Hz. exact (Nat.le_trans _ _ _ Hz Hle).
      + lia.
  Qed.

  (** Exact division by one is the identity, including all tracked fields. *)
  Lemma karr_divide_one : forall r, karr_divide 1 r = r.
  Proof.
    intro r. unfold karr_divide. destruct (karr_exact 1 r); [|reflexivity].
    destruct r as [zs rhs ms sc]. unfold karr_quotient. cbn [kcoeff kright kweight kscale].
    rewrite !Z.div_1_r.
    assert (Hmap : forall xs, map (fun z : Z => (z / 1)%Z) xs = xs).
    { intro xs. induction xs as [|z xs IH]; cbn [map]; [reflexivity|].
      now rewrite Z.div_1_r, IH. }
    now rewrite !Hmap.
  Qed.

  (** Subtraction adds at most one bit to the larger signed operand. *)
  Lemma karr_size_sub : forall x y,
    Z.size_nat (x - y) <= Nat.max (Z.size_nat x) (Z.size_nat y) + 1.
  Proof.
    intros x y. replace (x - y)%Z with (x + -y)%Z by ring.
    pose proof (karr_size_add x (-y)) as Hsize. now rewrite karr_size_opp in Hsize.
  Qed.

  (** A cross-product entry fits the sum of scalar and source widths plus one. *)
  Lemma karr_cross_entry_bits : forall a b x y bits,
    Z.size_nat a <= bits -> Z.size_nat b <= bits ->
    Z.size_nat x <= bits -> Z.size_nat y <= bits ->
    Z.size_nat (a * x - b * y) <= 2 * bits + 1.
  Proof.
    intros a b x y bits Ha Hb Hx Hy.
    pose proof (karr_size_mul a x). pose proof (karr_size_mul b y).
    pose proof (karr_size_sub (a * x) (b * y)). lia.
  Qed.

  (** The synchronized cross product never lengthens its left vector. *)
  Lemma karr_cross_length_le : forall a b xs ys,
    length (karr_cross a b xs ys) <= length xs.
  Proof.
    intros a b xs. induction xs as [|x xs IH]; intros [|y ys];
      cbn [karr_cross length]; try lia. pose proof (IH ys). lia.
  Qed.

  (** The cross product preserves a uniform entry budget with its one-step growth. *)
  Lemma karr_cross_bits : forall a b xs ys bits,
    Z.size_nat a <= bits -> Z.size_nat b <= bits ->
    Forall (fun z => Z.size_nat z <= bits) xs ->
    Forall (fun z => Z.size_nat z <= bits) ys ->
    Forall (fun z => Z.size_nat z <= 2 * bits + 1) (karr_cross a b xs ys).
  Proof.
    intros a b xs. induction xs as [|x xs IH]; intros [|y ys] bits Ha Hb Hxs Hys;
      cbn [karr_cross]; try solve [constructor].
    inversion Hxs as [|z zs Hx Htail]; subst z zs.
    inversion Hys as [|z zs Hy Htail']; subst z zs. constructor.
    - now apply karr_cross_entry_bits.
    - now apply IH.
  Qed.

  (** A row's leading coefficient fits its envelope even when the vector is empty. *)
  Lemma karr_head_bits : forall dim mlen bits r,
    karr_row_envelope dim mlen bits r -> Z.size_nat (karr_head r) <= bits.
  Proof.
    intros dim mlen bits r [_ [Hcoeff _]]. unfold karr_head.
    destruct (kcoeff r) as [|z zs]; [change (0 <= bits); lia|].
    now inversion Hcoeff.
  Qed.

  (** The initial projection reduction increases the entry budget only once. *)
  Lemma karr_reduce_one_envelope : forall dim mlen bits a b p r,
    Z.size_nat a <= bits -> Z.size_nat b <= bits ->
    karr_row_envelope dim mlen bits p -> karr_row_envelope dim mlen bits r ->
    karr_row_envelope dim mlen (2 * bits + 1) (karr_reduce 1 a b p r).
  Proof.
    intros dim mlen bits a b p r Ha Hb
      [Hpd [Hpc [Hpr [Hpm [Hpw Hps]]]]] [Hrd [Hrc [Hrr [Hrm [Hrw Hrs]]]]].
    unfold karr_reduce. rewrite karr_divide_one.
    unfold karr_row_envelope. cbn [kcoeff kright kweight kscale].
    split; [eapply Nat.le_trans; [apply karr_cross_length_le|exact Hrd]|].
    split; [now apply karr_cross_bits|].
    split; [now apply karr_cross_entry_bits|].
    split; [eapply Nat.le_trans; [apply karr_cross_length_le|exact Hrm]|].
    split; [now apply karr_cross_bits|]. now apply karr_cross_entry_bits.
  Qed.

  (** The undivided crossed row has one-step bit growth in every field. *)
  Lemma karr_cross_row_envelope : forall dim mlen bits a b p r,
    Z.size_nat a <= bits -> Z.size_nat b <= bits ->
    karr_row_envelope dim mlen bits p -> karr_row_envelope dim mlen bits r ->
    karr_row_envelope dim mlen (2 * bits + 1)
      (KRow (karr_cross a b (kcoeff r) (kcoeff p))
        (a * kright r - b * kright p)%Z
        (karr_cross a b (kweight r) (kweight p))
        (a * kscale r - b * kscale p)%Z).
  Proof.
    intros dim mlen bits a b p r Ha Hb
      [Hpd [Hpc [Hpr [Hpm [Hpw Hps]]]]]
      [Hrd [Hrc [Hrr [Hrm [Hrw Hrs]]]]].
    unfold karr_row_envelope. cbn [kcoeff kright kweight kscale].
    split; [eapply Nat.le_trans; [apply karr_cross_length_le|exact Hrd]|].
    split; [now apply karr_cross_bits|].
    split; [now apply karr_cross_entry_bits|].
    split; [eapply Nat.le_trans; [apply karr_cross_length_le|exact Hrm]|].
    split; [now apply karr_cross_bits|]. now apply karr_cross_entry_bits.
  Qed.

  (** Deleting and restoring the leading coordinate preserves bounded nonempty width. *)
  Lemma karr_restore_tail_envelope : forall dim mlen bits r, 1 <= dim ->
    karr_row_envelope dim mlen bits r ->
    karr_row_envelope dim mlen bits (karr_restore (karr_tail r)).
  Proof.
    intros dim mlen bits [zs rhs ms sc] Hpositive
      [Hdim [Hcoeff [Hrhs [Hmlen [Hmult Hscale]]]]].
    unfold karr_row_envelope, karr_restore, karr_tail.
    cbn [kcoeff kright kweight kscale] in *.
    destruct zs as [|z zs]; cbn [tl length] in *.
    - split; [exact Hpositive|]. split; [constructor; [change (0 <= bits); lia|constructor]|].
      repeat split; assumption.
    - split; [exact Hdim|]. split.
      + constructor; [change (0 <= bits); lia|]. now inversion Hcoeff.
      + repeat split; assumption.
  Qed.

  (** Projection's one Bareiss column leaves the row count unchanged. *)
  Lemma karr_bareiss_one_length : forall previous rows,
    length (karr_bareiss 1 previous rows) = length rows.
  Proof.
    intros previous rows. cbn [karr_bareiss].
    destruct (karr_pivot rows) as [[p rest]|] eqn:Hpivot.
    - cbn [length]. rewrite !length_map.
      pose proof (Permutation_length (proj2 (karr_pivot_some _ _ _ Hpivot))) as Hlength.
      cbn [length] in Hlength. lia.
    - now rewrite !length_map.
  Qed.

  (** One-column elimination has a direct width bound independent of general minors. *)
  Lemma karr_bareiss_one_envelopes : forall dim mlen bits rows, 1 <= dim ->
    Forall (karr_row_envelope dim mlen bits) rows ->
    Forall (karr_row_envelope dim mlen (2 * bits + 1)) (karr_bareiss 1 1 rows).
  Proof.
    intros dim mlen bits rows Hpositive Hrows. cbn [karr_bareiss].
    destruct (karr_pivot rows) as [[p rest]|] eqn:Hpivot.
    - assert (Hpermuted : Forall (karr_row_envelope dim mlen bits) (p :: rest)).
      { eapply Permutation_Forall; [exact (proj2 (karr_pivot_some _ _ _ Hpivot))|exact Hrows]. }
      inversion Hpermuted as [|q qs Hp Hrest]; subst q qs. constructor.
      + eapply (karr_row_envelope_mono dim mlen bits (2 * bits + 1)); [lia|exact Hp].
      + rewrite map_map. apply Forall_map, Forall_forall. intros r Hr.
        apply karr_restore_tail_envelope; [exact Hpositive|].
        pose proof (proj1 (Forall_forall _ _) Hrest r Hr) as Hrbound.
        apply karr_reduce_one_envelope; [| |exact Hp|exact Hrbound];
          eapply karr_head_bits; eassumption.
    - rewrite map_map. apply Forall_map, Forall_forall. intros r Hr.
      apply karr_restore_tail_envelope; [exact Hpositive|].
      eapply (karr_row_envelope_mono dim mlen bits (2 * bits + 1)); [lia|].
      exact (proj1 (Forall_forall _ _) Hrows r Hr).
  Qed.

  (** Repeated zeros use no arithmetic bits. *)
  Lemma karr_repeat_zero_bits : forall total,
    Forall (fun z => Z.size_nat z <= 1) (repeat 0%Z total).
  Proof.
    intro total. induction total as [|total IH]; cbn [repeat].
    - constructor.
    - constructor; [change (0 <= 1); lia|exact IH].
  Qed.

  (** Unit provenance vectors contain only zero and one. *)
  Lemma karr_unit_bits : forall total index,
    Forall (fun z => Z.size_nat z <= 1) (karr_unit total index).
  Proof.
    intro total. induction total as [|total IH]; intros [|index]; cbn [karr_unit].
    - constructor.
    - constructor.
    - constructor; [change (1 <= 1); lia|]. apply karr_repeat_zero_bits.
    - constructor; [change (0 <= 1); lia|apply IH].
  Qed.

  (** Seeding omits inequalities and emits at most one row per input row. *)
  Lemma karr_seed_rows_length : forall xs total index P,
    length (seed_rows xs total index P) <= length P.
  Proof.
    intros xs total index P. revert index. induction P as [|p P IH]; intro index;
      cbn [seed_rows length]; [lia|].
    specialize (IH (S index)). destruct (lrel p); cbn [length]; lia.
  Qed.

  (** Every emitted seed carries one multiplier slot per source row. *)
  Lemma karr_seed_weight_width : forall xs total index P,
    Forall (fun r => length (kweight r) = total)
      (seed_rows xs total index P).
  Proof.
    intros xs total index P. revert index.
    induction P as [|r P IH]; intro index; [constructor|].
    cbn [seed_rows]. destruct (lrel r).
    - constructor; [cbn [kweight]; apply karr_unit_length|apply IH].
    - apply IH.
  Qed.

  (** Dense lookup of a normal row preserves its declared arithmetic width. *)
  Lemma karr_dense_bits : forall xs r bits,
    NoDup (map fst (lhs r)) -> C.row_bits r <= bits ->
    Forall (fun z => Z.size_nat z <= bits) (dense xs r).
  Proof.
    intros xs r bits Hnormal Hbits. unfold dense. apply Forall_map, Forall_forall.
    intros x _. apply karr_coefficient_normal_bits; [exact Hnormal|].
    apply Forall_forall. intros p Hin. pose proof (karr_row_entry_bits r p Hin). lia.
  Qed.

  (** Normal rows seed bounded dense coordinates and unit provenance. *)
  Lemma karr_seed_rows_envelopes : forall xs total index P dim mlen bits,
    length xs <= dim -> total <= mlen -> 1 <= bits ->
    Forall (fun r => NoDup (map fst (lhs r)) /\ C.row_bits r <= bits) P ->
    Forall (karr_row_envelope dim mlen bits) (seed_rows xs total index P).
  Proof.
    intros xs total index P. revert index.
    induction P as [|p P IH]; intros index dim mlen bits Hdim Hmlen Hpositive Hrows;
      [constructor|].
    inversion Hrows as [|q qs [Hnormal Hbits] Htail]; subst q qs.
    cbn [seed_rows]. destruct (lrel p).
    - constructor.
      + unfold karr_row_envelope. cbn [kcoeff kright kweight kscale].
        split; [unfold dense; now rewrite length_map|].
        split; [now apply karr_dense_bits|]. split.
        * pose proof (karr_row_rhs_bits p). lia.
        * split; [now rewrite karr_unit_length|]. split.
          -- eapply Forall_impl; [|apply karr_unit_bits]. intros z Hz. exact (Nat.le_trans _ _ _ Hz Hpositive).
          -- change (0 <= bits). lia.
      + now apply IH.
    - now apply IH.
  Qed.

  (** Sparse reconstruction is no longer than its coordinate list. *)
  Lemma karr_sparse_length : forall xs zs, length (sparse xs zs) <= length xs.
  Proof.
    intros xs zs. unfold sparse. eapply Nat.le_trans; [apply filter_length_le|].
    rewrite length_combine. apply Nat.le_min_l.
  Qed.

  (** Sparse reconstruction preserves separate key and arithmetic-width envelopes. *)
  Lemma karr_sparse_row_bits : forall xs zs right_hand keys bits,
    Forall (fun x => X.bits x <= keys) xs ->
    Forall (fun z => Z.size_nat z <= bits) zs -> Z.size_nat right_hand <= bits ->
    C.row_key_bits (LCons X.t (sparse xs zs) REq right_hand) <= keys /\
      C.row_bits (LCons X.t (sparse xs zs) REq right_hand) <= bits.
  Proof.
    intros xs zs right_hand keys bits Hkeys Hcoeff Hrhs. split.
    - unfold C.row_key_bits. cbn [lhs]. apply karr_max_bound; [lia|].
      apply Forall_forall. intros [x z] Hin. cbn [fst].
      unfold sparse in Hin. apply filter_In in Hin as [Hin _].
      pose proof (in_combine_l _ _ _ _ Hin) as Hx.
      exact (proj1 (Forall_forall _ _) Hkeys x Hx).
    - unfold C.row_bits. cbn [lhs rhs]. apply karr_max_bound; [exact Hrhs|].
      apply Forall_forall. intros [x z] Hin. cbn [snd].
      unfold sparse in Hin. apply filter_In in Hin as [Hin _].
      pose proof (in_combine_r _ _ _ _ Hin) as Hz.
      exact (proj1 (Forall_forall _ _) Hcoeff z Hz).
  Qed.

  (** Three primitive clocks cover one signed cross-product coordinate. *)
  Lemma T_karr_cross_entry_bounded : forall a b x y bits,
    Z.size_nat a <= bits -> Z.size_nat b <= bits ->
    Z.size_nat x <= bits -> Z.size_nat y <= bits ->
    (Z.T_mul a x + Z.T_mul b y + Z.T_sub (a * x) (b * y) <=
      48 * N.of_nat ((bits + 1)^2))%N.
  Proof.
    intros a b x y bits Ha Hb Hx Hy.
    pose proof (karr_T_Z_mul_bilinear a x) as Hmulx.
    pose proof (karr_T_Z_mul_bilinear b y) as Hmuly.
    pose proof (karr_size_mul a x) as Hsizex.
    pose proof (karr_size_mul b y) as Hsizey.
    pose proof (Z.T_sub_le (a * x) (b * y)) as Hsub.
    rewrite karr_nat_square. rewrite !Nat2N.inj_add in *. cbn [N.of_nat] in *. nia.
  Qed.

  (** A vector cross product pays a quadratic arithmetic budget per visited entry. *)
  Lemma T_karr_cross_bounded : forall a b xs ys bits,
    Z.size_nat a <= bits -> Z.size_nat b <= bits ->
    Forall (fun z => Z.size_nat z <= bits) xs ->
    Forall (fun z => Z.size_nat z <= bits) ys ->
    (T_karr_cross a b xs ys <=
      64 * N.of_nat (length xs + 1) * N.of_nat ((bits + 1)^2))%N.
  Proof.
    intros a b xs. induction xs as [|x xs IH]; intros [|y ys] bits Ha Hb Hxs Hys.
    - time_unfold T_karr_cross. cbn [length].
      pose proof (karr_nat_square_ge (bits + 1) ltac:(lia)). nia.
    - time_unfold T_karr_cross. cbn [length].
      pose proof (karr_nat_square_ge (bits + 1) ltac:(lia)). nia.
    - time_unfold T_karr_cross. cbn [length].
      pose proof (karr_nat_square_ge (bits + 1) ltac:(lia)). nia.
    - inversion Hxs as [|z zs Hx Htail]; subst z zs.
      inversion Hys as [|z zs Hy Htail']; subst z zs.
      specialize (IH ys bits Ha Hb Htail Htail').
      pose proof (T_karr_cross_entry_bounded a b x y bits Ha Hb Hx Hy) as Hentry.
      pose proof (karr_nat_square_ge (bits + 1) ltac:(lia)) as Hsquare.
      time_unfold T_karr_cross. cbn [length]. time_simpl.
      rewrite !Nat2N.inj_add. cbn [N.of_nat]. nia.
  Qed.

  (** Division by one still charges the actual general signed-division implementation. *)
  Lemma T_karr_division_one_bounded : forall z bits, Z.size_nat z <= bits ->
    (Z.T_div z 1 <= 64 * N.of_nat ((bits + 1)^2))%N.
  Proof.
    intros z bits Hbits. pose proof (Z.T_div_le z 1) as Hdiv.
    change (Z.size_nat 1) with 1 in Hdiv.
    rewrite karr_nat_square. rewrite !Nat2N.inj_add in *. cbn [N.of_nat] in *. nia.
  Qed.

  (** Signed division is quadratic in a common dividend and divisor bit bound. *)
  Lemma T_karr_division_bounded : forall z d bits,
    Z.size_nat z <= bits -> Z.size_nat d <= bits ->
    (Z.T_div z d <= 64 * N.of_nat ((bits + 1)^2))%N.
  Proof.
    intros z d bits Hz Hd.
    pose proof (Z.T_div_le z d) as Hdiv.
    rewrite karr_nat_square. rewrite !Nat2N.inj_add in *.
    cbn [N.of_nat] in *. nia.
  Qed.

  (** Exactness testing pays the actual remainder clock and a constant zero test. *)
  Lemma T_karr_divisible_one_bounded : forall z bits, Z.size_nat z <= bits ->
    (T_karr_divisible 1 z <= 64 * N.of_nat ((bits + 1)^2))%N.
  Proof.
    intros z bits Hbits. pose proof (Z.T_modulo_le z 1) as Hmod.
    change (Z.size_nat 1) with 1 in Hmod.
    pose proof (T_karr_zero_test (z mod 1)) as Hzero.
    time_unfold T_karr_divisible. time_simpl.
    rewrite karr_nat_square. rewrite !Nat2N.inj_add in *. cbn [N.of_nat] in *. nia.
  Qed.

  (** Exactness testing is quadratic in the common signed operand width. *)
  Lemma T_karr_divisible_bounded : forall d z bits,
    Z.size_nat d <= bits -> Z.size_nat z <= bits ->
    (T_karr_divisible d z <= 64 * N.of_nat ((bits + 1)^2))%N.
  Proof.
    intros d z bits Hd Hz.
    pose proof (Z.T_modulo_le z d) as Hmod.
    pose proof (T_karr_zero_test (z mod d)) as Hzero.
    time_unfold T_karr_divisible. time_simpl.
    rewrite karr_nat_square. rewrite !Nat2N.inj_add in *.
    cbn [N.of_nat] in *. nia.
  Qed.

  (** Universal Boolean traversal needs callback bounds only for present entries. *)
  Lemma karr_T_forallb_members : forall A (f : A -> bool) (T_f : A -> N) k xs,
    (forall x, In x xs -> (T_f x <= k)%N) ->
    (List.T_forallb f T_f xs <= (k + 2) * N.of_nat (length xs) + 1)%N.
  Proof.
    intros A f T_f k xs. induction xs as [|x xs IH]; intro Hf.
    - time_unfold List.T_forallb. cbn [length]. lia.
    - pose proof (Hf x (or_introl eq_refl)) as Hhead.
      specialize (IH (fun y Hy => Hf y (or_intror Hy))).
      time_unfold List.T_forallb. cbn [length]. time_simpl. nia.
  Qed.


  (** Checking a row's common divisor scans both tracked vectors once. *)
  Lemma T_karr_exact_one_bounded : forall dim mlen bits r,
    karr_row_envelope dim mlen bits r ->
    (T_karr_exact 1 r <=
      256 * N.of_nat (dim + mlen + 1) * N.of_nat ((bits + 1)^2))%N.
  Proof.
    intros dim mlen bits r [Hdim [Hcoeff [Hrhs [Hmlen [Hmult Hscale]]]]].
    set (work := N.of_nat ((bits + 1)^2)).
    assert (Hpositive : (1 <= work)%N).
    { unfold work. pose proof (karr_nat_square_ge (bits + 1) ltac:(lia)). lia. }
    assert (Hcoefftime : (List.T_forallb (karr_divisible 1) (T_karr_divisible 1)
      (kcoeff r) <= (64 * work + 2) * N.of_nat (length (kcoeff r)) + 1)%N).
    { apply karr_T_forallb_members. intros z Hz. apply T_karr_divisible_one_bounded.
      exact (proj1 (Forall_forall _ _) Hcoeff z Hz). }
    assert (Hmulttime : (List.T_forallb (karr_divisible 1) (T_karr_divisible 1)
      (kweight r) <= (64 * work + 2) * N.of_nat (length (kweight r)) + 1)%N).
    { apply karr_T_forallb_members. intros z Hz. apply T_karr_divisible_one_bounded.
      exact (proj1 (Forall_forall _ _) Hmult z Hz). }
    pose proof (T_karr_divisible_one_bounded (kright r) bits Hrhs) as Hrighttime.
    pose proof (T_karr_divisible_one_bounded (kscale r) bits Hscale) as Hscaletime.
    pose proof (T_karr_zero_test 1) as Hdivisor.
    fold work in Hrighttime, Hscaletime |- *.
    time_unfold T_karr_exact. time_simpl.
    change (fun z : Z => T_karr_divisible 1 z) with (T_karr_divisible 1).
    rewrite !Nat2N.inj_add. cbn [N.of_nat].
    clear -Hdim Hmlen Hcoefftime Hmulttime Hrighttime Hscaletime Hpositive Hdivisor.
    clearbody work. nia.
  Qed.

  (** Checking exact division scans both vectors at a common operand width. *)
  Lemma T_karr_exact_bounded : forall dim mlen bits d r,
    Z.size_nat d <= bits -> karr_row_envelope dim mlen bits r ->
    (T_karr_exact d r <=
      256 * N.of_nat (dim + mlen + 1) * N.of_nat ((bits + 1)^2))%N.
  Proof.
    intros dim mlen bits d r Hd
      [Hdim [Hcoeff [Hrhs [Hmlen [Hmult Hscale]]]]].
    set (work := N.of_nat ((bits + 1)^2)).
    assert (Hpositive : (1 <= work)%N).
    { unfold work. pose proof (karr_nat_square_ge (bits + 1) ltac:(lia)). lia. }
    assert (Hcoefftime : (List.T_forallb (karr_divisible d) (T_karr_divisible d)
      (kcoeff r) <= (64 * work + 2) * N.of_nat (length (kcoeff r)) + 1)%N).
    { apply karr_T_forallb_members. intros z Hz.
      apply T_karr_divisible_bounded; [exact Hd|].
      exact (proj1 (Forall_forall _ _) Hcoeff z Hz). }
    assert (Hmulttime : (List.T_forallb (karr_divisible d) (T_karr_divisible d)
      (kweight r) <= (64 * work + 2) * N.of_nat (length (kweight r)) + 1)%N).
    { apply karr_T_forallb_members. intros z Hz.
      apply T_karr_divisible_bounded; [exact Hd|].
      exact (proj1 (Forall_forall _ _) Hmult z Hz). }
    pose proof (T_karr_divisible_bounded d (kright r) bits Hd Hrhs) as Hrighttime.
    pose proof (T_karr_divisible_bounded d (kscale r) bits Hd Hscale) as Hscaletime.
    pose proof (T_karr_zero_test d) as Hdivisor.
    fold work in Hrighttime, Hscaletime |- *.
    time_unfold T_karr_exact. time_simpl.
    change (fun z : Z => T_karr_divisible d z) with (T_karr_divisible d).
    rewrite !Nat2N.inj_add. cbn [N.of_nat].
    clear -Hdim Hmlen Hcoefftime Hmulttime Hrighttime Hscaletime Hpositive Hdivisor.
    clearbody work. nia.
  Qed.

  (** Applying the exact quotient scans both vectors and the scalar fields once. *)
  Lemma T_karr_quotient_one_bounded : forall dim mlen bits r,
    karr_row_envelope dim mlen bits r ->
    (T_karr_quotient 1 r <=
      256 * N.of_nat (dim + mlen + 1) * N.of_nat ((bits + 1)^2))%N.
  Proof.
    intros dim mlen bits r [Hdim [Hcoeff [Hrhs [Hmlen [Hmult Hscale]]]]].
    set (work := N.of_nat ((bits + 1)^2)).
    assert (Hpositive : (1 <= work)%N).
    { unfold work. pose proof (karr_nat_square_ge (bits + 1) ltac:(lia)). lia. }
    assert (Hcoefftime : (ListDef.T_map (fun z => (z / 1)%Z)
      (fun z => (1 + Z.T_div z 1)%N) (kcoeff r) <=
      (65 * work + 1) * N.of_nat (length (kcoeff r)) + 1)%N).
    { apply karr_T_map_members. intros z Hz.
      pose proof (T_karr_division_one_bounded z bits
        (proj1 (Forall_forall _ _) Hcoeff z Hz)) as Hdiv.
      fold work in Hdiv. lia. }
    assert (Hmulttime : (ListDef.T_map (fun z => (z / 1)%Z)
      (fun z => (1 + Z.T_div z 1)%N) (kweight r) <=
      (65 * work + 1) * N.of_nat (length (kweight r)) + 1)%N).
    { apply karr_T_map_members. intros z Hz.
      pose proof (T_karr_division_one_bounded z bits
        (proj1 (Forall_forall _ _) Hmult z Hz)) as Hdiv.
      fold work in Hdiv. lia. }
    pose proof (T_karr_division_one_bounded (kright r) bits Hrhs) as Hrighttime.
    pose proof (T_karr_division_one_bounded (kscale r) bits Hscale) as Hscaletime.
    fold work in Hrighttime, Hscaletime |- *.
    time_unfold T_karr_quotient. time_simpl.
    rewrite !Nat2N.inj_add. cbn [N.of_nat].
    clear -Hdim Hmlen Hcoefftime Hmulttime Hrighttime Hscaletime Hpositive.
    clearbody work. nia.
  Qed.

  (** Quotient construction scans both vectors at a common operand width. *)
  Lemma T_karr_quotient_bounded : forall dim mlen bits d r,
    Z.size_nat d <= bits -> karr_row_envelope dim mlen bits r ->
    (T_karr_quotient d r <=
      256 * N.of_nat (dim + mlen + 1) * N.of_nat ((bits + 1)^2))%N.
  Proof.
    intros dim mlen bits d r Hd
      [Hdim [Hcoeff [Hrhs [Hmlen [Hmult Hscale]]]]].
    set (work := N.of_nat ((bits + 1)^2)).
    assert (Hpositive : (1 <= work)%N).
    { unfold work. pose proof (karr_nat_square_ge (bits + 1) ltac:(lia)). lia. }
    assert (Hcoefftime : (ListDef.T_map (fun z => (z / d)%Z)
      (fun z => (1 + Z.T_div z d)%N) (kcoeff r) <=
      (65 * work + 1) * N.of_nat (length (kcoeff r)) + 1)%N).
    { apply karr_T_map_members. intros z Hz.
      pose proof (T_karr_division_bounded z d bits
        (proj1 (Forall_forall _ _) Hcoeff z Hz) Hd) as Hdiv.
      fold work in Hdiv. lia. }
    assert (Hmulttime : (ListDef.T_map (fun z => (z / d)%Z)
      (fun z => (1 + Z.T_div z d)%N) (kweight r) <=
      (65 * work + 1) * N.of_nat (length (kweight r)) + 1)%N).
    { apply karr_T_map_members. intros z Hz.
      pose proof (T_karr_division_bounded z d bits
        (proj1 (Forall_forall _ _) Hmult z Hz) Hd) as Hdiv.
      fold work in Hdiv. lia. }
    pose proof (T_karr_division_bounded (kright r) d bits Hrhs Hd) as Hrighttime.
    pose proof (T_karr_division_bounded (kscale r) d bits Hscale Hd) as Hscaletime.
    fold work in Hrighttime, Hscaletime |- *.
    time_unfold T_karr_quotient. time_simpl.
    rewrite !Nat2N.inj_add. cbn [N.of_nat].
    clear -Hdim Hmlen Hcoefftime Hmulttime Hrighttime Hscaletime Hpositive.
    clearbody work. nia.
  Qed.

  (** Guarding exact division is bounded by the sum of its check and quotient paths. *)
  Lemma T_karr_divide_one_bounded : forall dim mlen bits r,
    karr_row_envelope dim mlen bits r ->
    (T_karr_divide 1 r <=
      1024 * N.of_nat (dim + mlen + 1) * N.of_nat ((bits + 1)^2))%N.
  Proof.
    intros dim mlen bits r Hrow.
    pose proof (T_karr_exact_one_bounded dim mlen bits r Hrow) as Hcheck.
    pose proof (T_karr_quotient_one_bounded dim mlen bits r Hrow) as Hdivide.
    pose proof (karr_nat_square_ge (bits + 1) ltac:(lia)) as Hpositive.
    time_unfold T_karr_divide. destruct (karr_exact 1 r); time_simpl;
      rewrite !Nat2N.inj_add in *; cbn [N.of_nat] in *; nia.
  Qed.

  (** Guarded division costs the same quadratic budget for any bounded divisor. *)
  Lemma T_karr_divide_bounded : forall dim mlen bits d r,
    Z.size_nat d <= bits -> karr_row_envelope dim mlen bits r ->
    (T_karr_divide d r <=
      1024 * N.of_nat (dim + mlen + 1) * N.of_nat ((bits + 1)^2))%N.
  Proof.
    intros dim mlen bits d r Hd Hrow.
    pose proof (T_karr_exact_bounded dim mlen bits d r Hd Hrow) as Hcheck.
    pose proof (T_karr_quotient_bounded dim mlen bits d r Hd Hrow) as Hdivide.
    pose proof (karr_nat_square_ge (bits + 1) ltac:(lia)) as Hpositive.
    time_unfold T_karr_divide. destruct (karr_exact d r); time_simpl;
      rewrite !Nat2N.inj_add in *; cbn [N.of_nat] in *; nia.
  Qed.

  (** The first reduction charges two cross products and exact division by one. *)
  Lemma T_karr_reduce_one_bounded : forall dim mlen bits a b p r,
    Z.size_nat a <= bits -> Z.size_nat b <= bits ->
    karr_row_envelope dim mlen bits p -> karr_row_envelope dim mlen bits r ->
    (T_karr_reduce 1 a b p r <=
      8192 * N.of_nat (dim + mlen + 1) * N.of_nat ((bits + 1)^2))%N.
  Proof.
    intros dim mlen bits a b p r Ha Hb Hp Hr.
    pose proof (karr_reduce_one_envelope dim mlen bits a b p r Ha Hb Hp Hr) as Hraw.
    unfold karr_reduce in Hraw. rewrite karr_divide_one in Hraw.
    pose proof (T_karr_divide_one_bounded dim mlen (2 * bits + 1) _ Hraw) as Hdivide.
    replace ((2 * bits + 1 + 1)^2) with (4 * (bits + 1)^2) in Hdivide
      by (clear -bits; cbn [Nat.pow]; nia).
    destruct Hp as [Hpd [Hpc [Hpr [Hpm [Hpw Hps]]]]].
    destruct Hr as [Hrd [Hrc [Hrr [Hrm [Hrw Hrs]]]]].
    pose proof (T_karr_cross_bounded a b (kcoeff r) (kcoeff p) bits Ha Hb Hrc Hpc)
      as Hcoefftime.
    pose proof (T_karr_cross_bounded a b (kweight r) (kweight p) bits Ha Hb Hrw Hpw)
      as Hmulttime.
    pose proof (T_karr_cross_entry_bounded a b (kright r) (kright p) bits Ha Hb Hrr Hpr)
      as Hrighttime.
    pose proof (T_karr_cross_entry_bounded a b (kscale r) (kscale p) bits Ha Hb Hrs Hps)
      as Hscaletime.
    rewrite Nat2N.inj_mul in Hdivide.
    set (work := N.of_nat ((bits + 1)^2)) in *.
    assert (Hpositive : (1 <= work)%N).
    { unfold work. pose proof (karr_nat_square_ge (bits + 1) ltac:(lia)). lia. }
    time_unfold T_karr_reduce. time_simpl.
    clear -Hcoefftime Hmulttime Hrighttime Hscaletime Hdivide Hrd Hrm Hpositive.
    clearbody work. rewrite !Nat2N.inj_add in *. cbn [N.of_nat] in *. nia.
  Qed.

  (** A general pivot reduction charges crosses and exact guarded division. *)
  Lemma T_karr_reduce_bounded : forall dim mlen bits d a b p r,
    Z.size_nat d <= bits -> Z.size_nat a <= bits -> Z.size_nat b <= bits ->
    karr_row_envelope dim mlen bits p -> karr_row_envelope dim mlen bits r ->
    (T_karr_reduce d a b p r <=
      8192 * N.of_nat (dim + mlen + 1) * N.of_nat ((bits + 1)^2))%N.
  Proof.
    intros dim mlen bits d a b p r Hd Ha Hb Hp Hr.
    pose proof (karr_cross_row_envelope dim mlen bits a b p r Ha Hb Hp Hr) as Hraw.
    pose proof (T_karr_divide_bounded dim mlen (2 * bits + 1) d _
      ltac:(lia) Hraw) as Hdivide.
    replace ((2 * bits + 1 + 1)^2) with (4 * (bits + 1)^2) in Hdivide
      by (clear -bits; cbn [Nat.pow]; nia).
    destruct Hp as [Hpd [Hpc [Hpr [Hpm [Hpw Hps]]]]].
    destruct Hr as [Hrd [Hrc [Hrr [Hrm [Hrw Hrs]]]]].
    pose proof (T_karr_cross_bounded a b (kcoeff r) (kcoeff p) bits Ha Hb Hrc Hpc)
      as Hcoefftime.
    pose proof (T_karr_cross_bounded a b (kweight r) (kweight p) bits Ha Hb Hrw Hpw)
      as Hmulttime.
    pose proof (T_karr_cross_entry_bounded a b (kright r) (kright p) bits Ha Hb Hrr Hpr)
      as Hrighttime.
    pose proof (T_karr_cross_entry_bounded a b (kscale r) (kscale p) bits Ha Hb Hrs Hps)
      as Hscaletime.
    rewrite Nat2N.inj_mul in Hdivide.
    set (work := N.of_nat ((bits + 1)^2)) in *.
    assert (Hpositive : (1 <= work)%N).
    { unfold work. pose proof (karr_nat_square_ge (bits + 1) ltac:(lia)). lia. }
    time_unfold T_karr_reduce. time_simpl.
    clear -Hcoefftime Hmulttime Hrighttime Hscaletime Hdivide Hrd Hrm Hpositive.
    clearbody work. rewrite !Nat2N.inj_add in *. cbn [N.of_nat] in *. nia.
  Qed.

  (** Reading a leading coefficient has a fixed record-and-list dispatch cost. *)
  Lemma T_karr_head_bounded : forall r, (T_karr_head r <= 4)%N.
  Proof.
    intros [zs rhs ms sc]. time_unfold T_karr_head. cbn [kcoeff].
    destruct zs; time_simpl; lia.
  Qed.

  (** Removing a coefficient uses a fixed number of field reads and one list dispatch. *)
  Lemma T_karr_tail_bounded : forall r, (T_karr_tail r <= 8)%N.
  Proof.
    intros [zs rhs ms sc]. time_unfold T_karr_tail. time_unfold (@List.T_tl).
    cbn [kcoeff kright kweight kscale]. destruct zs; time_simpl; lia.
  Qed.

  (** Restoring a zero coefficient has a constant construction charge. *)
  Lemma T_karr_restore_bounded : forall r, (T_karr_restore r <= 8)%N.
  Proof.
    intros [zs rhs ms sc]. time_unfold T_karr_restore. time_simpl. lia.
  Qed.

  (** Pivot discovery tests each visited head against zero in constant time. *)
  Lemma T_karr_pivot_bounded : forall rows,
    (T_karr_pivot rows <= 16 * N.of_nat (length rows + 1))%N.
  Proof.
    intro rows. induction rows as [|r rows IH].
    - time_unfold T_karr_pivot. cbn [length]. lia.
    - pose proof (T_karr_head_bounded r) as Hhead.
      pose proof (T_karr_zero_test (karr_head r)) as Hzero.
      time_unfold T_karr_pivot. destruct (Z.eqb (karr_head r) 0).
      + destruct (karr_pivot rows) as [[p rest]|]; time_simpl;
          cbn [length]; rewrite !Nat2N.inj_add in *; cbn [N.of_nat] in *; nia.
      + time_simpl. cbn [length]. rewrite !Nat2N.inj_add. cbn [N.of_nat]. nia.
  Qed.

  (** The first-nonzero lookup tests each scanned coefficient once. *)
  Lemma T_karr_first_bounded : forall entries,
    (T_karr_first entries <= 16 * N.of_nat (length entries + 1))%N.
  Proof.
    intro entries. induction entries as [|z entries IH].
    - time_unfold T_karr_first. cbn [length]. lia.
    - pose proof (T_karr_zero_test z) as Hzero.
      time_unfold T_karr_first. destruct (Z.eqb z 0).
      + destruct (karr_first entries) as [[i a]|]; time_simpl;
          cbn [length]; rewrite !Nat2N.inj_add in *; cbn [N.of_nat] in *; nia.
      + time_simpl. cbn [length]. rewrite !Nat2N.inj_add. cbn [N.of_nat]. nia.
  Qed.

  (** A dense coordinate lookup scans no more than the source row length. *)
  Lemma T_karr_nth_bounded : forall index entries,
    (T_karr_nth index entries <= 8 * N.of_nat (length entries + 1))%N.
  Proof.
    intro index. induction index as [|index IH]; intros [|z entries];
      time_unfold T_karr_nth; cbn [length]; try lia.
    pose proof (IH entries) as Htail.
    rewrite !Nat2N.inj_add in *. cbn [N.of_nat] in *. lia.
  Qed.

  (** Testing a full coefficient vector for zero costs one fixed scan per entry. *)
  Lemma T_karr_zero_bounded : forall r,
    (T_karr_zero r <= 8 * N.of_nat (length (kcoeff r) + 1))%N.
  Proof.
    intro r.
    assert (Hzero : forall z, (Z.T_eqb 0 z <= 2)%N).
    { intros [|p|p]; time_unfold Z.T_eqb; time_simpl; lia. }
    pose proof (karr_T_forallb_members Z (Z.eqb 0)
      (fun z => Z.T_eqb 0 z) 2 (kcoeff r)
      (fun z _ => Hzero z)) as Hscan.
    time_unfold T_karr_zero. time_unfold T_kcoeff.
    change (fun z : Z => Z.T_eqb 0 z) with (fun z => Z.T_eqb 0 z).
    rewrite Nat2N.inj_add. cbn [N.of_nat].
    change (N.pos (PosDef.Pos.of_succ_nat 0)) with 1%N.
    lia.
  Qed.

  (** A projection reduction removes the coordinate just eliminated by its cross product. *)
  Definition karr_projection_step (a : Z) (p r : karr_row) : karr_row :=
    karr_tail (karr_reduce 1 a (karr_head r) p r).

  TimeFun karr_projection_step.

  (** One mapped row update includes its head read, reduction and tail removal. *)
  Lemma T_karr_projection_step_bounded : forall dim mlen bits a p r,
    Z.size_nat a <= bits ->
    karr_row_envelope dim mlen bits p -> karr_row_envelope dim mlen bits r ->
    (T_karr_projection_step a p r <=
      16384 * N.of_nat (dim + mlen + 1) * N.of_nat ((bits + 1)^2))%N.
  Proof.
    intros dim mlen bits a p r Ha Hp Hr.
    pose proof (T_karr_reduce_one_bounded dim mlen bits a (karr_head r) p r Ha
      (karr_head_bits dim mlen bits r Hr) Hp Hr) as Hreduce.
    pose proof (T_karr_head_bounded r) as Hhead.
    pose proof (T_karr_tail_bounded (karr_reduce 1 a (karr_head r) p r)) as Htail.
    set (work := (N.of_nat (dim + mlen + 1) * N.of_nat ((bits + 1)^2))%N).
    assert (Hpositive : (1 <= work)%N).
    { unfold work. assert (Hdim : (1 <= N.of_nat (dim + mlen + 1))%N) by lia.
      pose proof (karr_nat_square_ge (bits + 1) ltac:(lia)) as Hbits. nia. }
    replace (8192 * N.of_nat (dim + mlen + 1) * N.of_nat ((bits + 1)^2))%N with
      (8192 * work)%N in Hreduce by (unfold work; ring).
    replace (16384 * N.of_nat (dim + mlen + 1) * N.of_nat ((bits + 1)^2))%N with
      (16384 * work)%N by (unfold work; ring).
    time_unfold T_karr_projection_step. time_simpl.
    clear -Hreduce Hhead Htail Hpositive. clearbody work. nia.
  Qed.

  (** One general mapped pivot step includes its head, reduction and tail clocks. *)
  Lemma T_karr_pivot_step_bounded : forall dim mlen bits d a p r,
    Z.size_nat d <= bits -> Z.size_nat a <= bits ->
    karr_row_envelope dim mlen bits p -> karr_row_envelope dim mlen bits r ->
    (4 + T_karr_head r +
      T_karr_reduce d a (karr_head r) p r +
      T_karr_tail (karr_reduce d a (karr_head r) p r) <=
      16384 * N.of_nat (dim + mlen + 1) * N.of_nat ((bits + 1)^2))%N.
  Proof.
    intros dim mlen bits d a p r Hd Ha Hp Hr.
    pose proof (T_karr_reduce_bounded dim mlen bits d a (karr_head r) p r
      Hd Ha (karr_head_bits dim mlen bits r Hr) Hp Hr) as Hreduce.
    pose proof (T_karr_head_bounded r) as Hhead.
    pose proof (T_karr_tail_bounded
      (karr_reduce d a (karr_head r) p r)) as Htail.
    assert (Hwork : (1 <= N.of_nat (dim + mlen + 1) *
      N.of_nat ((bits + 1)^2))%N).
    { assert (Hdim : (1 <= N.of_nat (dim + mlen + 1))%N) by lia.
      pose proof (karr_nat_square_ge (bits + 1) ltac:(lia)) as Hbits. nia. }
    nia.
  Qed.

  (** The zero-column recursion has constant dispatch cost. *)
  Lemma T_karr_bareiss_zero_bounded : forall previous rows,
    (T_karr_bareiss 0 previous rows <= 4)%N.
  Proof.
    intros previous rows. time_unfold T_karr_bareiss. lia.
  Qed.

  (** One full projection column charges its row updates and two list traversals. *)
  Lemma T_karr_bareiss_one_bounded : forall dim mlen bits rows,
    Forall (karr_row_envelope dim mlen bits) rows ->
    (T_karr_bareiss 1 1 rows <= 32768 * N.of_nat (length rows + 1) *
      N.of_nat (dim + mlen + 1) * N.of_nat ((bits + 1)^2))%N.
  Proof.
    intros dim mlen bits rows Hrows.
    set (work := (N.of_nat (dim + mlen + 1) * N.of_nat ((bits + 1)^2))%N).
    assert (Hpositive : (1 <= work)%N).
    { unfold work. assert (Hdim : (1 <= N.of_nat (dim + mlen + 1))%N) by lia.
      pose proof (karr_nat_square_ge (bits + 1) ltac:(lia)) as Hbits. nia. }
    pose proof (T_karr_pivot_bounded rows) as Hpivot_time.
    replace (32768 * N.of_nat (length rows + 1) * N.of_nat (dim + mlen + 1) *
      N.of_nat ((bits + 1)^2))%N with (32768 * N.of_nat (length rows + 1) * work)%N
      by (unfold work; ring).
    time_unfold T_karr_bareiss.
    destruct (karr_pivot rows) as [[p rest]|] eqn:Hpivot.
    - destruct (karr_pivot_some _ _ _ Hpivot) as [_ Hperm].
      assert (Hpermuted : Forall (karr_row_envelope dim mlen bits) (p :: rest)).
      { eapply Permutation_Forall; [exact Hperm|exact Hrows]. }
      inversion Hpermuted as [|q qs Hp Hrest]; subst q qs.
      pose proof (Permutation_length Hperm) as Hlength. cbn [length] in Hlength.
      pose proof (T_karr_head_bounded p) as Hhead.
      assert (Hstep : forall r, In r rest ->
        (T_karr_projection_step (karr_head p) p r <= 16384 * work)%N).
      { intros r Hr.
        replace (16384 * work)%N with (16384 * N.of_nat (dim + mlen + 1) *
          N.of_nat ((bits + 1)^2))%N by (unfold work; ring).
        apply T_karr_projection_step_bounded.
        - now apply karr_head_bits with (dim := dim) (mlen := mlen).
        - exact Hp.
        - exact (proj1 (Forall_forall _ _) Hrest r Hr). }
      pose proof (karr_T_map_members karr_row karr_row
        (karr_projection_step (karr_head p) p) (T_karr_projection_step (karr_head p) p)
        (16384 * work)%N rest Hstep) as Hstep_map.
      pose proof (karr_T_map_members karr_row karr_row karr_restore T_karr_restore 8
        (map (karr_projection_step (karr_head p) p) rest)
        (fun r _ => T_karr_restore_bounded r)) as Hrestore.
      rewrite length_map in Hrestore.
      pose proof (T_karr_bareiss_zero_bounded (karr_head p)
        (map (karr_projection_step (karr_head p) p) rest)) as Hbase.
      change (fun r => karr_tail (karr_reduce 1 (karr_head p) (karr_head r) p r)) with
        (karr_projection_step (karr_head p) p).
      time_simpl.
      lazymatch goal with
      | |- context [ListDef.T_map (karr_projection_step (karr_head p) p) ?Tf rest] =>
        change Tf with (T_karr_projection_step (karr_head p) p)
      end.
      change (fun r : karr_row => T_karr_restore r) with T_karr_restore.
      cbn [karr_bareiss].
      clear -Hpositive Hpivot_time Hlength Hhead Hstep_map Hrestore Hbase.
      clearbody work. rewrite !Nat2N.inj_add in *. cbn [N.of_nat] in *. nia.
    - pose proof (karr_T_map_members karr_row karr_row karr_tail T_karr_tail 8 rows
        (fun r _ => T_karr_tail_bounded r)) as Htail.
      pose proof (karr_T_map_members karr_row karr_row karr_restore T_karr_restore 8
        (map karr_tail rows) (fun r _ => T_karr_restore_bounded r)) as Hrestore.
      rewrite length_map in Hrestore.
      pose proof (T_karr_bareiss_zero_bounded 1 (map karr_tail rows)) as Hbase.
      time_simpl. change (fun r : karr_row => T_karr_tail r) with T_karr_tail.
      change (fun r : karr_row => T_karr_restore r) with T_karr_restore.
      cbn [karr_bareiss].
      clear -Hpositive Hpivot_time Htail Hrestore Hbase. clearbody work.
      rewrite !Nat2N.inj_add in *. cbn [N.of_nat] in *. nia.
  Qed.

  (** One arbitrary Bareiss column pays for its pivot, updates and restores. *)
  Lemma T_karr_bareiss_stage_bounded : forall cols previous rows dim mlen bits,
    Z.size_nat previous <= bits ->
    Forall (karr_row_envelope dim mlen bits) rows ->
    (T_karr_bareiss (S cols) previous rows <=
      32768 * N.of_nat (length rows + 1) *
        N.of_nat (dim + mlen + 1) * N.of_nat ((bits + 1)^2) +
      match karr_pivot rows with
      | None => T_karr_bareiss cols previous (map karr_tail rows)
      | Some (pivot, rest) =>
          T_karr_bareiss cols (karr_head pivot)
            (map (fun row => karr_tail
              (karr_reduce previous (karr_head pivot) (karr_head row) pivot row))
              rest)
      end)%N.
  Proof.
    intros cols previous rows dim mlen bits Hprevious Hrows.
    set (work := (N.of_nat (dim + mlen + 1) * N.of_nat ((bits + 1)^2))%N).
    assert (Hpositive : (1 <= work)%N).
    { unfold work. assert (Hdim : (1 <= N.of_nat (dim + mlen + 1))%N) by lia.
      pose proof (karr_nat_square_ge (bits + 1) ltac:(lia)) as Hbits. nia. }
    pose proof (T_karr_pivot_bounded rows) as Hpivot_time.
    time_unfold T_karr_bareiss.
    destruct (karr_pivot rows) as [[pivot rest]|] eqn:Hselect.
    - destruct (karr_pivot_some _ _ _ Hselect) as [_ Hperm].
      assert (Hpermuted : Forall (karr_row_envelope dim mlen bits)
        (pivot :: rest)).
      { eapply Permutation_Forall; [exact Hperm|exact Hrows]. }
      apply Forall_cons_iff in Hpermuted as [Hp Hrest].
      pose proof (Permutation_length Hperm) as Hlength.
      cbn [length] in Hlength.
      pose proof (T_karr_head_bounded pivot) as Hhead.
      set (step := fun row => karr_tail
        (karr_reduce previous (karr_head pivot) (karr_head row) pivot row)).
      set (T_step := fun row => (1 + (T_karr_head row +
        T_karr_reduce previous (karr_head pivot) (karr_head row) pivot row +
        T_karr_tail
          (karr_reduce previous (karr_head pivot) (karr_head row) pivot row)))%N).
      assert (Hstep : forall row, In row rest -> (T_step row <= 16384 * work)%N).
      { intros row Hrow. unfold T_step.
        pose proof (T_karr_pivot_step_bounded dim mlen bits previous
          (karr_head pivot) pivot row Hprevious
          (karr_head_bits dim mlen bits pivot Hp) Hp
          (proj1 (Forall_forall _ _) Hrest row Hrow)) as Htime.
        replace (16384 * N.of_nat (dim + mlen + 1) *
          N.of_nat ((bits + 1)^2))%N with (16384 * work)%N in Htime
          by (unfold work; ring).
        clearbody work. nia. }
      pose proof (karr_T_map_members karr_row karr_row step T_step
        (16384 * work)%N rest Hstep) as Hstep_map.
      pose proof (karr_T_map_members karr_row karr_row karr_restore T_karr_restore 8
        (karr_bareiss cols (karr_head pivot) (map step rest))
        (fun row _ => T_karr_restore_bounded row)) as Hrestore.
      rewrite karr_bareiss_length, length_map in Hrestore.
      time_simpl.
      lazymatch goal with
      | |- context [ListDef.T_map ?f ?Tf rest] =>
        change f with step; change Tf with T_step
      end.
      change (fun row : karr_row => T_karr_restore row) with T_karr_restore.
      fold step.
      clear -Hpositive Hpivot_time Hlength Hhead Hstep_map Hrestore.
      replace (32768 * N.of_nat (length rows + 1) *
        N.of_nat (dim + mlen + 1) * N.of_nat ((bits + 1)^2))%N with
        (32768 * N.of_nat (length rows + 1) * work)%N
        by (unfold work; ring).
      clearbody work. clearbody step. clearbody T_step.
      rewrite !Nat2N.inj_add in *.
      rewrite Hlength in *.
      rewrite !Nat2N.inj_succ in *.
      change (N.of_nat 1) with 1%N in *.
      set (n := N.of_nat (length rest)) in *.
      clearbody n.
      cbn [N.of_nat] in *.
      replace (N.succ n) with (n + 1)%N in * by lia.
      change (N.succ 0) with 1%N in *.
      replace ((16384 * work + 1) * n)%N with
        (16384 * (n * work) + n)%N in Hstep_map by ring.
      replace (32768 * (n + 1 + 1) * work)%N with
        (32768 * (n * work) + 65536 * work)%N by ring.
      assert (Hvolume : (n <= n * work)%N).
      { replace n with (n * 1)%N at 1 by ring.
        now apply N.mul_le_mono_l. }
      set (volume := (n * work)%N) in *.
      set (pivot_cost := T_karr_pivot rows) in *.
      set (head_cost := T_karr_head pivot) in *.
      set (step_cost := ListDef.T_map step T_step rest) in *.
      set (recursive_cost := T_karr_bareiss cols (karr_head pivot)
        (map step rest)) in *.
      set (restore_cost := ListDef.T_map karr_restore T_karr_restore
        (karr_bareiss cols (karr_head pivot) (map step rest))) in *.
      clearbody volume pivot_cost head_cost step_cost recursive_cost restore_cost.
      lia.
    - pose proof (karr_T_map_members karr_row karr_row karr_tail T_karr_tail 8 rows
        (fun row _ => T_karr_tail_bounded row)) as Htail.
      pose proof (karr_T_map_members karr_row karr_row karr_restore T_karr_restore 8
        (karr_bareiss cols previous (map karr_tail rows))
        (fun row _ => T_karr_restore_bounded row)) as Hrestore.
      rewrite karr_bareiss_length, length_map in Hrestore.
      time_simpl.
      change (fun row : karr_row => T_karr_tail row) with T_karr_tail.
      change (fun row : karr_row => T_karr_restore row) with T_karr_restore.
      clear -Hpositive Hpivot_time Htail Hrestore.
      rewrite !Nat2N.inj_add in *. cbn [N.of_nat] in *.
      change (N.pos (PosDef.Pos.of_succ_nat 0)) with 1%N in *.
      replace (N.of_nat dim + N.of_nat mlen + 1)%N with
        (N.of_nat (dim + mlen + 1))%N by lia.
      set (n := N.of_nat (length rows)) in *.
      clearbody n.
      replace (32768 * (n + 1) * N.of_nat (dim + mlen + 1) *
        N.of_nat ((bits + 1)^2))%N with
        (32768 * ((n + 1) * work))%N in |- * by (unfold work; ring).
      clearbody work.
      assert (Hvolume : (n + 1 <= (n + 1) * work)%N).
      { replace (n + 1)%N with ((n + 1) * 1)%N at 1 by ring.
        now apply N.mul_le_mono_l. }
      set (volume := ((n + 1) * work)%N) in *.
      set (pivot_cost := T_karr_pivot rows) in *.
      set (tail_cost := ListDef.T_map karr_tail T_karr_tail rows) in *.
      set (recursive_cost := T_karr_bareiss cols previous (map karr_tail rows)) in *.
      set (restore_cost := ListDef.T_map karr_restore T_karr_restore
        (karr_bareiss cols previous (map karr_tail rows))) in *.
      clearbody volume pivot_cost tail_cost recursive_cost restore_cost.
      lia.
  Qed.

  (** One uniform charge covers each remaining column of a bounded run. *)
  Definition karr_bareiss_stage_budget (budget bits : nat) : N :=
    (32768 * N.of_nat (budget + 1) * N.of_nat (budget + budget + 1) *
      N.of_nat ((bits + 1)^2))%N.

  (** The partition in the run state bounds its live row count. *)
  Lemma karr_run_state_row_count : forall width cols original previous
      pivot_rows pivot_columns columns labels rows,
    karr_run_state width cols original previous pivot_rows pivot_columns
      columns labels rows -> length rows <= length original.
  Proof.
    intros width cols original previous pivot_rows pivot_columns columns labels
      rows Hstate.
    unfold karr_run_state in Hstate.
    destruct Hstate as [_ [_ [Hlabels [_ [_ [_ [_ [Hpartition _]]]]]]]].
    apply Permutation_length in Hpartition.
    rewrite length_app in Hpartition. lia.
  Qed.

  (** Summing the stage charge follows the exact labeled elimination trace. *)
  Lemma T_karr_bareiss_run_bounded : forall width cols original previous
      pivot_rows pivot_columns columns labels rows budget bits,
    karr_run_state width cols original previous pivot_rows pivot_columns
      columns labels rows ->
    length original <= budget -> length columns <= budget ->
    (forall z, In z (karr_signed_minors width original) -> Z.size_nat z <= bits) ->
    (T_karr_bareiss cols previous rows <=
      N.of_nat cols * karr_bareiss_stage_budget budget bits + 4)%N.
  Proof.
    intros width cols. induction cols as [|cols IH];
      intros original previous pivot_rows pivot_columns columns labels rows
        budget bits Hstate Horiginal Hcolumns Hbits.
    - pose proof (T_karr_bareiss_zero_bounded previous rows) as Hzero.
      cbn [N.of_nat N.mul N.add]. exact Hzero.
    - assert (Hcolumn_count : S cols <= length columns).
      { unfold karr_run_state in Hstate.
        destruct Hstate as [_ [_ [_ [_ [_ [Hcount _]]]]]]. exact Hcount. }
      destruct columns as [|head columns]; [cbn [length] in Hcolumn_count; lia|].
      pose proof (karr_run_state_previous_minor width (S cols) original
        previous pivot_rows pivot_columns (head :: columns) labels rows Hstate)
        as Hprevious_member.
      pose proof (karr_run_state_envelope width (S cols) original previous
        pivot_rows pivot_columns (head :: columns) labels rows budget bits Hstate
        Hcolumns Hbits) as Hrows.
      pose proof (T_karr_bareiss_stage_bounded cols previous rows budget budget
        bits (Hbits previous Hprevious_member) Hrows) as Hstage.
      assert (Hrow_count : length rows <= budget).
      { pose proof (karr_run_state_row_count width (S cols) original previous
          pivot_rows pivot_columns (head :: columns) labels rows Hstate).
        lia. }
      assert (Hstage_cost :
        (32768 * N.of_nat (length rows + 1) *
          N.of_nat (budget + budget + 1) * N.of_nat ((bits + 1)^2) <=
          karr_bareiss_stage_budget budget bits)%N).
      { unfold karr_bareiss_stage_budget.
        set (work := (N.of_nat (budget + budget + 1) *
          N.of_nat ((bits + 1)^2))%N).
        replace (32768 * N.of_nat (length rows + 1) *
          N.of_nat (budget + budget + 1) * N.of_nat ((bits + 1)^2))%N with
          (32768 * N.of_nat (length rows + 1) * work)%N
          by (unfold work; ring).
        replace (32768 * N.of_nat (budget + 1) *
          N.of_nat (budget + budget + 1) * N.of_nat ((bits + 1)^2))%N with
          (32768 * N.of_nat (budget + 1) * work)%N
          by (unfold work; ring).
        apply N.mul_le_mono_r. apply N.mul_le_mono_l. lia. }
      assert (Htail_budget : length columns <= budget).
      { cbn [length] in Hcolumns. lia. }
      destruct (karr_pivot rows) as [[pivot rest]|] eqn:Hselect.
      + destruct (karr_run_state_pivot width cols original previous pivot_rows
          pivot_columns head columns labels rows pivot rest Hstate Hselect)
          as [origin [remaining Hnext]].
        specialize (IH original (karr_head pivot) (pivot_rows ++ [origin])
          (pivot_columns ++ [head]) columns remaining
          (map (fun row => karr_tail
            (karr_reduce previous (karr_head pivot) (karr_head row) pivot row))
            rest) budget bits Hnext Horiginal Htail_budget Hbits).
        cbn [N.of_nat] in IH |- *.
        eapply N.le_trans; [exact Hstage|].
        eapply N.le_trans; [apply N.add_le_mono; [exact Hstage_cost|exact IH]|].
        change (N.pos (PosDef.Pos.of_succ_nat cols)) with (N.of_nat (S cols)).
        rewrite Nat2N.inj_succ.
        replace (N.succ (N.of_nat cols)) with (N.of_nat cols + 1)%N by lia.
        replace (((N.of_nat cols + 1) * karr_bareiss_stage_budget budget bits + 4)%N)
          with (karr_bareiss_stage_budget budget bits +
            (N.of_nat cols * karr_bareiss_stage_budget budget bits + 4))%N
          by ring.
        apply N.le_refl.
      + pose proof (karr_run_state_skip width cols original previous pivot_rows
          pivot_columns head columns labels rows Hstate) as Hnext.
        specialize (IH original previous pivot_rows pivot_columns columns labels
          (map karr_tail rows) budget bits Hnext Horiginal Htail_budget Hbits).
        cbn [N.of_nat] in IH |- *.
        eapply N.le_trans; [exact Hstage|].
        eapply N.le_trans; [apply N.add_le_mono; [exact Hstage_cost|exact IH]|].
        change (N.pos (PosDef.Pos.of_succ_nat cols)) with (N.of_nat (S cols)).
        rewrite Nat2N.inj_succ.
        replace (N.succ (N.of_nat cols)) with (N.of_nat cols + 1)%N by lia.
        replace (((N.of_nat cols + 1) * karr_bareiss_stage_budget budget bits + 4)%N)
          with (karr_bareiss_stage_budget budget bits +
            (N.of_nat cols * karr_bareiss_stage_budget budget bits + 4))%N
          by ring.
        apply N.le_refl.
  Qed.


  Definition karr_prepare_factor : N := (karr_raw_normal_factor + 32)%N.

  (** Sharing normalized rows pays their total raw mass rather than a product of row lengths. *)
  Lemma T_karr_prepare_rows_bounded : forall P keys bits total,
    Forall (fun r => C.row_key_bits r <= keys /\ C.row_bits r <= bits) P ->
    terms (Reached P) <= total ->
    (ListDef.T_map normalize_row T_normalize_row P <=
      karr_prepare_factor * N.of_nat (terms (Reached P) + length P + 1) *
        N.of_nat (keys + bits + Nat.log2 total + 1))%N.
  Proof.
    intro P. induction P as [|p P IH]; intros keys bits total Hrows Htotal.
    - time_unfold ListDef.T_map. cbn [terms rows_of map fold_right length].
      unfold karr_prepare_factor. rewrite !Nat2N.inj_add. cbn [N.of_nat]. nia.
    - inversion Hrows as [|q qs [Hkey Hbits] Htail]; subst q qs.
      change (length (lhs p) + terms (Reached P) <= total) in Htotal.
      specialize (IH keys bits total Htail ltac:(lia)).
      assert (Hentries : Forall (fun q => Pos.size_nat (X.encode (fst q)) <= keys /\
        Z.size_nat (snd q) <= bits) (lhs p)).
      { apply Forall_forall. intros q Hq.
        pose proof (karr_row_key_member p q Hq).
        pose proof (karr_row_entry_bits p q Hq). split; lia. }
      pose proof (T_karr_normal_log (lhs p) keys bits Hentries) as Hnormal.
      pose proof (Nat.log2_le_mono (length (lhs p)) total ltac:(lia)) as Hlog.
      assert (Hrowtime : (T_normalize_row p <= karr_raw_normal_factor *
        N.of_nat (length (lhs p) + 1) * N.of_nat (keys + bits + Nat.log2 total + 1) + 8)%N).
      { assert (Hnormal_total : (T_normalize_coef (lhs p) <= karr_raw_normal_factor *
          N.of_nat (length (lhs p) + 1) * N.of_nat (keys + bits + Nat.log2 total + 1))%N).
        { eapply N.le_trans; [exact Hnormal|]. apply N.mul_le_mono_l. lia. }
        time_unfold T_normalize_row. time_simpl. nia. }
      set (work := N.of_nat (keys + bits + Nat.log2 total + 1)) in *.
      assert (Hpositive : (1 <= work)%N) by (unfold work; lia).
      time_unfold ListDef.T_map. time_simpl.
      change (terms (Reached (p :: P))) with (length (lhs p) + terms (Reached P)).
      cbn [length]. unfold karr_prepare_factor in *.
      clear -IH Hrowtime Hpositive. clearbody work.
      rewrite !Nat2N.inj_add in *. cbn [N.of_nat] in *. nia.
  Qed.

  (** Every linear-form entry fits its combined key and coefficient width. *)
  Lemma karr_form_entry_bits : forall f p, In p (coef f) ->
    X.bits (fst p) + Z.size_nat (snd p) <= F.form_bits f.
  Proof.
    intros f p Hp. unfold F.form_bits.
    exact (karr_max_member _ (fun q => X.bits (fst q) + Z.size_nat (snd q))
      (Z.size_nat (cst f)) (coef f) p Hp).
  Qed.

  (** A form's constant fits the same maximum as its coefficient entries. *)
  Lemma karr_form_constant_bits : forall f, Z.size_nat (cst f) <= F.form_bits f.
  Proof.
    intro f. unfold F.form_bits. apply karr_max_seed.
  Qed.

  Definition karr_negate_term (p : X.t * Z) : X.t * Z := (fst p, (- snd p)%Z).
  TimeFun karr_negate_term.

  (** Negating a stored coefficient only changes its outer sign constructor. *)
  Lemma T_karr_negate_term_bounded : forall p, (T_karr_negate_term p <= 8)%N.
  Proof.
    intros [x z]. pose proof (Z.T_opp_le z).
    time_unfold T_karr_negate_term. time_simpl. lia.
  Qed.

  (** Form subtraction retains the raw entry widths before equal keys are merged. *)
  Lemma karr_atom_input_sizes : forall a bits,
    F.form_bits (al a) + F.form_bits (ar a) <= bits ->
    Forall (fun p => Pos.size_nat (X.encode (fst p)) <= bits /\
      Z.size_nat (snd p) <= bits)
      (coef (al a) ++ map karr_negate_term (coef (ar a))).
  Proof.
    intros a bits Hbits. apply Forall_app. split.
    - apply Forall_forall. intros p Hp.
      pose proof (karr_form_entry_bits (al a) p Hp). unfold X.bits in *. split; lia.
    - apply Forall_map, Forall_forall. intros p Hp.
      pose proof (karr_form_entry_bits (ar a) p Hp).
      cbn [karr_negate_term fst snd]. rewrite karr_size_opp.
      unfold X.bits in *. split; lia.
  Qed.

  (** An atom normalizer pays for its source lengths and logarithmic merge width. *)
  Lemma T_karr_atom_normal_bounded : forall a count bits,
    length (coef (al a)) + length (coef (ar a)) <= count ->
    F.form_bits (al a) + F.form_bits (ar a) <= bits ->
    (T_normalize_coef (coef (al a) ++ map karr_negate_term (coef (ar a))) <=
      (2 * karr_raw_normal_factor) * N.of_nat (count + 1) *
        N.of_nat (bits + Nat.log2 count + 1))%N.
  Proof.
    intros a count bits Hlength Hbits.
    pose proof (T_karr_normal_log _ bits bits (karr_atom_input_sizes a bits Hbits)) as Hnormal.
    assert (Hcount : length (coef (al a) ++ map karr_negate_term (coef (ar a))) <= count).
    { rewrite length_app, length_map. exact Hlength. }
    pose proof (Nat.log2_le_mono _ _ Hcount) as Hlog.
    eapply N.le_trans; [exact Hnormal|].
    replace (2 * karr_raw_normal_factor * N.of_nat (count + 1) *
      N.of_nat (bits + Nat.log2 count + 1))%N with
      (karr_raw_normal_factor * N.of_nat (count + 1) *
        (2 * N.of_nat (bits + Nat.log2 count + 1)))%N by ring.
    apply N.mul_le_mono; [apply N.mul_le_mono_l; lia|lia].
  Qed.

  Definition karr_atom_factor : N := (2 * karr_raw_normal_factor + 64)%N.

  (** Converting one equality atom pays for sign changes, subtraction and normalization. *)
  Lemma T_karr_atom_rows_bounded : forall a count bits,
    length (coef (al a)) + length (coef (ar a)) <= count ->
    F.form_bits (al a) + F.form_bits (ar a) <= bits ->
    (T_atom_rows a <= karr_atom_factor * N.of_nat (count + 1) *
      N.of_nat (bits + Nat.log2 count + 1))%N.
  Proof.
    intros a count bits Hlength Hbits.
    pose proof (T_karr_atom_normal_bounded a count bits Hlength Hbits) as Hnormal.
    pose proof (karr_T_map_members _ _ karr_negate_term T_karr_negate_term 8
      (coef (ar a)) ltac:(intros p _; apply T_karr_negate_term_bounded)) as Hnegate.
    pose proof (Datatypes.T_app_le (coef (al a))
      (map karr_negate_term (coef (ar a)))) as Happ.
    pose proof (Z.T_sub_le (cst (ar a)) (cst (al a))) as Hsubtract.
    pose proof (karr_form_constant_bits (al a)) as Hleft.
    pose proof (karr_form_constant_bits (ar a)) as Hright.
    set (work := (N.of_nat (count + 1) *
      N.of_nat (bits + Nat.log2 count + 1))%N).
    assert (Hcount_work : (N.of_nat (count + 1) <= work)%N).
    { unfold work. rewrite <- (N.mul_1_r (N.of_nat (count + 1))) at 1.
      apply N.mul_le_mono_l. lia. }
    assert (Hbits_work : (N.of_nat (bits + 1) <= work)%N).
    { unfold work. rewrite <- (N.mul_1_l (N.of_nat (bits + 1))) at 1.
      apply N.mul_le_mono; lia. }
    assert (Hpositive : (1 <= work)%N) by lia.
    assert (Hnormal_total : (T_normalize_coef
      (coef (al a) ++ map karr_negate_term (coef (ar a))) <=
        (2 * karr_raw_normal_factor) * work)%N).
    { unfold work. rewrite N.mul_assoc. exact Hnormal. }
    assert (Hnegate_total : (ListDef.T_map karr_negate_term T_karr_negate_term
      (coef (ar a)) <= 10 * work)%N).
    { clear -Hnegate Hcount_work Hlength. nia. }
    assert (Happ_total : (Datatypes.T_app (coef (al a))
      (map karr_negate_term (coef (ar a))) <= work)%N) by lia.
    assert (Hsubtract_total : (Z.T_sub (cst (ar a)) (cst (al a)) <= 3 * work)%N).
    { assert (Hlinear : (Z.T_sub (cst (ar a)) (cst (al a)) <=
        3 * N.of_nat (bits + 1))%N) by lia.
      eapply N.le_trans; [exact Hlinear|]. now apply N.mul_le_mono_l. }
    replace (karr_atom_factor * N.of_nat (count + 1) *
      N.of_nat (bits + Nat.log2 count + 1))%N with (karr_atom_factor * work)%N
      by (unfold work; ring).
    time_unfold T_atom_rows.
    change (fun p : X.t * Z => (fst p, (- snd p)%Z)) with karr_negate_term.
    lazymatch goal with
    | |- context [ListDef.T_map karr_negate_term ?Tf (coef (ar a))] =>
      change Tf with T_karr_negate_term
    end.
    destruct (alw a), (arw a), (acmp a); time_simpl;
      try time_unfold T_normalize_row; time_simpl.
    all: cbn [lhs].
    all: clear -Hnormal_total Hnegate_total Happ_total Hsubtract_total Hpositive.
    all: clearbody work; unfold karr_atom_factor; nia.
  Qed.

  (** Equality-atom conversion emits at most one stored row. *)
  Lemma karr_atom_rows_length : forall a, length (atom_rows a) <= 1.
  Proof.
    intro a. unfold atom_rows. destruct (alw a), (arw a), (acmp a); cbn [length]; lia.
  Qed.

  (** A flat map with singleton-or-empty outputs pays only a constant append per input. *)
  Lemma karr_T_flat_map_singleton : forall (A B : Type) (f : A -> list B)
      (T_f : A -> N) factor xs,
    (forall x, In x xs -> length (f x) <= 1) ->
    (forall x, In x xs -> (T_f x <= factor)%N) ->
    (List.T_flat_map f T_f xs <= (factor + 4) * N.of_nat (length xs) + 1)%N.
  Proof.
    intros A B f T_f factor xs. induction xs as [|x xs IH]; intros Hlength Htime.
    - time_unfold List.T_flat_map. cbn [length]. lia.
    - pose proof (Hlength x (or_introl eq_refl)) as Hhead_length.
      pose proof (Htime x (or_introl eq_refl)) as Hhead_time.
      specialize (IH ltac:(intros y Hy; apply Hlength; now right)
        ltac:(intros y Hy; apply Htime; now right)).
      pose proof (Datatypes.T_app_le (f x) (flat_map f xs)) as Happ.
      time_unfold List.T_flat_map. cbn [length]. time_simpl. nia.
  Qed.

  (** Singleton-or-empty flattening never exceeds its source length. *)
  Lemma karr_flat_map_singleton_length : forall (A B : Type) (f : A -> list B) xs,
    (forall x, In x xs -> length (f x) <= 1) -> length (flat_map f xs) <= length xs.
  Proof.
    intros A B f xs. induction xs as [|x xs IH]; intro Hlength.
    - reflexivity.
    - pose proof (Hlength x (or_introl eq_refl)) as Hhead.
      specialize (IH ltac:(intros y Hy; apply Hlength; now right)).
      cbn [flat_map length]. rewrite length_app. lia.
  Qed.

  (** Changing the initial sum from zero to one adds exactly one. *)
  Lemma karr_fold_add_one : forall xs,
    fold_right Nat.add 1 xs = fold_right Nat.add 0 xs + 1.
  Proof.
    induction xs as [|x xs IH]; cbn [fold_right]; lia.
  Qed.

  (** The cubic elimination allowance covers quadratic atom count at linear width. *)
  Lemma karr_assume_atom_budget : forall dim count bits width,
    count + 1 <= dim -> bits <= width ->
    (count + 1)^2 * (bits + Nat.log2 count + 1) <=
      dim^3 * (ellB dim width + 1)^2.
  Proof.
    intros dim count bits width Hcount Hbits.
    assert (Hdim : 1 <= dim) by lia.
    pose proof (Nat.log2_le_mono count dim ltac:(lia)) as Hlog.
    assert (Hwidth : bits + Nat.log2 count + 1 <= ellB dim width + 1).
    { unfold ellB. nia. }
    apply Nat.mul_le_mono.
    - eapply Nat.le_trans; [apply Nat.pow_le_mono_l; exact Hcount|].
      cbn [Nat.pow]. nia.
    - eapply Nat.le_trans; [exact Hwidth|]. cbn [Nat.pow]. nia.
  Qed.

  (** The same allowance pays a linear traversal of each source row and its width. *)
  Lemma karr_assume_source_budget : forall dim rows bits width,
    rows + 1 <= dim -> bits <= width ->
    (rows + 1) * (bits + 1) <= dim^3 * (ellB dim width + 1)^2.
  Proof.
    intros dim rows bits width Hrows Hbits.
    assert (Hdim : 1 <= dim) by lia.
    assert (Hwidth : bits + 1 <= ellB dim width + 1) by (unfold ellB; nia).
    apply Nat.mul_le_mono.
    - eapply Nat.le_trans; [exact Hrows|]. cbn [Nat.pow]. nia.
    - eapply Nat.le_trans; [exact Hwidth|]. cbn [Nat.pow]. nia.
  Qed.

  Definition karr_assume_factor : N := (karr_prepare_factor + 2 * karr_atom_factor + 64)%N.

  (** Assumptions normalize raw sources and every emitted equality within the frozen budget. *)
  Lemma T_karr_assume_bounded : forall g es s,
    (T_assume g es s <= karr_assume_factor * N.of_nat (assume_work g es s + 1))%N.
  Proof.
    intros g es [|P].
    - time_unfold T_assume. unfold karr_assume_factor. time_simpl. nia.
    - set (count := fold_right Nat.add 0 (map tsize es)).
      set (bits := F.bits_es g es).
      set (dim := n (Reached P) + count + 1).
      set (source_bits := nell (Reached P)).
      set (allowance := dim^3 * (ellB dim (source_bits + bits) + 1)^2).
      set (work := N.of_nat (assume_work g es (Reached P) + 1)).
      assert (Hallowance : (N.of_nat allowance <= work)%N).
      { unfold work, assume_work, allowance, dim, source_bits, bits, count. lia. }
      assert (Hsource_nat : (length P + 1) * (source_bits + 1) <= allowance).
      { unfold allowance. apply karr_assume_source_budget; [unfold dim, n; cbn [rows_of]; lia|lia]. }
      assert (Hatom_nat : (count + 1)^2 * (bits + Nat.log2 count + 1) <= allowance).
      { unfold allowance. apply karr_assume_atom_budget; [unfold dim; lia|lia]. }
      assert (Hcount_work : (N.of_nat (count + 1) <= work)%N).
      { eapply N.le_trans; [|exact Hallowance].
        assert (Hnat : count + 1 <= allowance).
        { eapply Nat.le_trans; [|exact Hatom_nat].
          clear -count bits. cbn [Nat.pow]. nia. }
        clear -Hnat. lia. }
      assert (Hpositive : (1 <= work)%N) by lia.
      assert (Hlin : (F.T_atoms_of g es <= work)%N).
      { unfold work, assume_work. rewrite !Nat2N.inj_add, N2Nat.id. lia. }
      destruct (F.atoms_of_size g es) as [Hnumber Hsizes].
      rewrite karr_fold_add_one in Hnumber. fold count bits in Hnumber, Hsizes.
      assert (Hatoms : forall a, In a (F.atoms_of g es) ->
        (T_atom_rows a <= karr_atom_factor * N.of_nat (count + 1) *
          N.of_nat (bits + Nat.log2 count + 1))%N).
      { intros a Ha. destruct (proj1 (Forall_forall _ _) Hsizes a Ha) as [Hlength Hbits].
        apply T_karr_atom_rows_bounded; [exact Hlength|lia]. }
      pose proof (karr_T_flat_map_singleton _ _ atom_rows T_atom_rows
        (karr_atom_factor * N.of_nat (count + 1) *
          N.of_nat (bits + Nat.log2 count + 1))%N (F.atoms_of g es)
        ltac:(intros a _; apply karr_atom_rows_length) Hatoms) as Hflat.
      pose proof (karr_flat_map_singleton_length _ _ atom_rows (F.atoms_of g es)
        ltac:(intros a _; apply karr_atom_rows_length)) as Hflat_length.
      assert (Hatom_product : (N.of_nat (length (F.atoms_of g es)) *
        N.of_nat (count + 1) * N.of_nat (bits + Nat.log2 count + 1) <= 2 * work)%N).
      { assert (Hnat : length (F.atoms_of g es) * (count + 1) *
          (bits + Nat.log2 count + 1) <= 2 * allowance).
        { eapply Nat.le_trans with (m := 2 * ((count + 1)^2 *
            (bits + Nat.log2 count + 1))).
          - clear -Hnumber. cbn [Nat.pow]. nia.
          - lia. }
        rewrite <- !Nat2N.inj_mul. clear -Hnat Hallowance. lia. }
      assert (Hflat_total : (List.T_flat_map atom_rows T_atom_rows (F.atoms_of g es) <=
        (2 * karr_atom_factor + 12) * work)%N).
      { clear -Hflat Hatom_product Hnumber Hcount_work Hpositive. clearbody work. nia. }
      pose proof (Datatypes.T_app_le (flat_map atom_rows (F.atoms_of g es))
        (map normalize_row P)) as Happ.
      assert (Happ_total : (Datatypes.T_app (flat_map atom_rows (F.atoms_of g es))
        (map normalize_row P) <= 3 * work)%N).
      { clear -Happ Hflat_length Hnumber Hcount_work Hpositive. clearbody work. nia. }
      set (source_keys := fold_right Nat.max 0 (map C.row_key_bits P)).
      set (source_values := fold_right Nat.max 0 (map C.row_bits P)).
      assert (Hrows : Forall (fun r => C.row_key_bits r <= source_keys /\
        C.row_bits r <= source_values) P).
      { apply Forall_forall. intros r Hr. split; apply karr_max_member; exact Hr. }
      pose proof (T_karr_prepare_rows_bounded P source_keys source_values
        (terms (Reached P)) Hrows (Nat.le_refl _)) as Hmap.
      assert (Hsource_width : source_keys + source_values + Nat.log2 (terms (Reached P)) + 1 =
        source_bits).
      { unfold source_keys, source_values, source_bits, nell, ell. cbn [rows_of]. lia. }
      rewrite Hsource_width in Hmap.
      assert (Hmap_charge : (N.of_nat (terms (Reached P) + length P + 1) *
        N.of_nat source_bits <= work)%N).
      { assert (Hnat : (terms (Reached P) + length P + 1) * source_bits <=
          terms (Reached P) * (source_bits + 1) + allowance).
        { clear -Hsource_nat. clearbody allowance source_bits. nia. }
        rewrite <- Nat2N.inj_mul. unfold work, assume_work.
        change (N.of_nat ((terms (Reached P) + length P + 1) * source_bits) <=
          N.of_nat (terms (Reached P) * (source_bits + 1) + allowance +
            N.to_nat (F.T_atoms_of g es) + 1))%N.
        clear -Hnat. lia. }
      assert (Hmap_total : (ListDef.T_map normalize_row T_normalize_row P <=
        karr_prepare_factor * work)%N).
      { eapply N.le_trans; [exact Hmap|]. rewrite <- N.mul_assoc.
        now apply N.mul_le_mono_l. }
      time_unfold T_assume. time_simpl.
      change (fun a => T_atom_rows a) with T_atom_rows.
      change (fun r => T_normalize_row r) with T_normalize_row.
      fold work. unfold karr_assume_factor.
      clear -Hflat_total Happ_total Hmap_total Hlin Hpositive. clearbody work. nia.
  Qed.



  (** Repeating a zero has one constructor charge per vector position. *)
  Lemma T_karr_repeat_zero_bounded : forall total,
    (@ListDef.T_repeat Z 0%Z total <= N.of_nat total + 1)%N.
  Proof.
    intro total. induction total as [|total IH]; time_unfold (@ListDef.T_repeat);
      time_simpl; lia.
  Qed.

  (** The unit-vector constructor is linear in its requested total width. *)
  Lemma T_karr_unit_bounded : forall total index,
    (T_karr_unit total index <= 4 * N.of_nat (total + 1))%N.
  Proof.
    intro total. induction total as [|total IH]; intros [|index]; time_unfold T_karr_unit.
    - cbn [length]. lia.
    - cbn [length]. lia.
    - pose proof (T_karr_repeat_zero_bounded total) as Hrepeat.
      time_simpl. rewrite Nat2N.inj_add. cbn [N.of_nat]. nia.
    - pose proof (IH index) as Htail.
      time_simpl. rewrite Nat2N.inj_add. cbn [N.of_nat]. nia.
  Qed.

  (** This callback is the actual lookup performed for one dense coordinate. *)
  Definition karr_dense_lookup (r : lcons X.t) (x : X.t) : Z := coefficient x (lhs r).

  TimeFun karr_dense_lookup.

  Definition karr_lookup_factor : N := (8 * (karr_coefficient_factor + 4) + 16)%N.

  (** A dense lookup pays the raw row scan within a common matrix budget. *)
  Lemma T_karr_dense_lookup_bounded : forall r x dim bits,
    length (lhs r) <= dim -> C.row_bits r <= bits -> X.bits x <= bits ->
    (T_karr_dense_lookup r x <= karr_lookup_factor *
      N.of_nat (dim + 1) * N.of_nat (bits + dim + 1))%N.
  Proof.
    intros r x dim bits Hdim Hbits Hx.
    assert (Hentries : Forall (fun p => Z.size_nat (snd p) <= bits) (lhs r)).
    { apply Forall_forall. intros p Hp. pose proof (karr_row_entry_bits r p Hp). lia. }
    pose proof (T_karr_coefficient_bounded x (lhs r) bits Hentries) as Hcoef.
    assert (Hwidth : X.bits x + 2 * bits + length (lhs r) + 1 <= 3 * (bits + dim + 1))
      by lia.
    assert (Hscaled : (T_coefficient x (lhs r) <=
      3 * (karr_coefficient_factor + 4) * N.of_nat (dim + 1) *
        N.of_nat (bits + dim + 1))%N).
    { eapply N.le_trans; [exact Hcoef|].
      assert (Htransport : (N.of_nat (X.bits x + 2 * bits + length (lhs r) + 1) <=
        3 * N.of_nat (bits + dim + 1))%N).
      { replace (3 * N.of_nat (bits + dim + 1))%N with
          (N.of_nat (3 * (bits + dim + 1))) by (rewrite Nat2N.inj_mul; reflexivity). lia. }
      replace (3 * (karr_coefficient_factor + 4) * N.of_nat (dim + 1) *
        N.of_nat (bits + dim + 1))%N with
        (((karr_coefficient_factor + 4) * N.of_nat (dim + 1)) *
          (3 * N.of_nat (bits + dim + 1)))%N by ring.
      apply N.mul_le_mono.
      - apply N.mul_le_mono_l. lia.
      - exact Htransport. }
    set (work := (N.of_nat (dim + 1) * N.of_nat (bits + dim + 1))%N).
    assert (Hpositive : (1 <= work)%N).
    { unfold work. assert (Hd : (1 <= N.of_nat (dim + 1))%N) by lia.
      assert (Hb : (1 <= N.of_nat (bits + dim + 1))%N) by lia. nia. }
    replace (3 * (karr_coefficient_factor + 4) * N.of_nat (dim + 1) *
      N.of_nat (bits + dim + 1))%N with
      (3 * (karr_coefficient_factor + 4) * work)%N in Hscaled by (unfold work; ring).
    replace (karr_lookup_factor * N.of_nat (dim + 1) *
      N.of_nat (bits + dim + 1))%N with (karr_lookup_factor * work)%N
      by (unfold work; ring).
    time_unfold T_karr_dense_lookup. time_simpl. unfold karr_lookup_factor.
    clear -Hscaled Hpositive. clearbody work. nia.
  Qed.

  Definition karr_dense_factor : N := (karr_lookup_factor + 8)%N.

  (** Constructing dense coefficients scans the source row once per coordinate. *)
  Lemma T_karr_dense_bounded : forall xs r dim bits,
    length xs <= dim -> length (lhs r) <= dim -> C.row_bits r <= bits ->
    Forall (fun x => X.bits x <= bits) xs ->
    (T_dense xs r <= karr_dense_factor * N.of_nat (dim + 1)^2 *
      N.of_nat (bits + dim + 1))%N.
  Proof.
    intros xs r dim bits Hxs Hrow Hbits Hkeys.
    pose proof (karr_T_map_members X.t Z (karr_dense_lookup r) (T_karr_dense_lookup r)
      (karr_lookup_factor * N.of_nat (dim + 1) * N.of_nat (bits + dim + 1))%N xs
      ltac:(intros x Hx; apply T_karr_dense_lookup_bounded; [exact Hrow|exact Hbits|];
        exact (proj1 (Forall_forall _ _) Hkeys x Hx))) as Hmap.
    time_unfold T_dense.
    change (fun x => coefficient x (lhs r)) with (karr_dense_lookup r).
    time_simpl.
    lazymatch goal with
    | |- context [ListDef.T_map (karr_dense_lookup r) ?Tf xs] =>
      change Tf with (T_karr_dense_lookup r)
    end.
    set (work := (N.of_nat (dim + 1) * N.of_nat (bits + dim + 1))%N).
    assert (Hpositive : (1 <= work)%N).
    { unfold work. assert (Hd : (1 <= N.of_nat (dim + 1))%N) by lia.
      assert (Hb : (1 <= N.of_nat (bits + dim + 1))%N) by lia. nia. }
    replace (karr_lookup_factor * N.of_nat (dim + 1) *
      N.of_nat (bits + dim + 1))%N with (karr_lookup_factor * work)%N in Hmap
      by (unfold work; ring).
    replace (karr_dense_factor * N.of_nat (dim + 1)^2 *
      N.of_nat (bits + dim + 1))%N with
      (karr_dense_factor * N.of_nat (dim + 1) * work)%N
      by (unfold work; rewrite N.pow_2_r; ring).
    unfold karr_dense_factor. clear -Hmap Hxs Hpositive. clearbody work.
    rewrite !Nat2N.inj_add in *. cbn [N.of_nat] in *. nia.
  Qed.

  Definition karr_seed_factor : N := (karr_dense_factor + 32)%N.

  (** Matrix initialization charges every source header, dense scan and unit vector. *)
  Lemma T_karr_seed_rows_bounded : forall xs total index P dim bits,
    length xs <= dim -> total <= dim ->
    Forall (fun x => X.bits x <= bits) xs ->
    Forall (fun r => length (lhs r) <= dim /\ C.row_bits r <= bits) P ->
    (T_seed_rows xs total index P <= karr_seed_factor *
      N.of_nat (length P + 1) * N.of_nat (dim + 1)^2 * N.of_nat (bits + dim + 1))%N.
  Proof.
    intros xs total index P. revert index.
    induction P as [|p P IH]; intros index dim bits Hxs Htotal Hkeys Hrows.
    - time_unfold T_seed_rows. cbn [length]. unfold karr_seed_factor.
      rewrite !N.pow_2_r, !Nat2N.inj_add. cbn [N.of_nat]. nia.
    - inversion Hrows as [|q qs [Hrow Hbits] Htail]; subst q qs.
      pose proof (IH (S index) dim bits Hxs Htotal Hkeys Htail) as Hrest.
      pose proof (T_karr_dense_bounded xs p dim bits Hxs Hrow Hbits Hkeys) as Hdense.
      pose proof (T_karr_unit_bounded total index) as Hunit.
      set (work := (N.of_nat (dim + 1)^2 * N.of_nat (bits + dim + 1))%N).
      assert (Hextent : (N.of_nat (dim + 1) <= work)%N).
      { unfold work. rewrite N.pow_2_r.
        assert (Hfirst : (1 <= N.of_nat (dim + 1))%N) by lia.
        assert (Hsecond : (1 <= N.of_nat (bits + dim + 1))%N) by lia. nia. }
      assert (Hpositive : (1 <= work)%N) by (eapply N.le_trans; [|exact Hextent]; lia).
      assert (Hunit_total : (T_karr_unit total index <= 4 * work)%N).
      { eapply N.le_trans; [exact Hunit|]. apply N.mul_le_mono_l. lia. }
      replace (karr_seed_factor * N.of_nat (length P + 1) * N.of_nat (dim + 1)^2 *
        N.of_nat (bits + dim + 1))%N with
        (karr_seed_factor * N.of_nat (length P + 1) * work)%N in Hrest
        by (unfold work; ring).
      replace (karr_dense_factor * N.of_nat (dim + 1)^2 * N.of_nat (bits + dim + 1))%N
        with (karr_dense_factor * work)%N in Hdense by (unfold work; ring).
      replace (karr_seed_factor * N.of_nat (length (p :: P) + 1) *
        N.of_nat (dim + 1)^2 * N.of_nat (bits + dim + 1))%N with
        (karr_seed_factor * N.of_nat (length (p :: P) + 1) * work)%N
        by (unfold work; ring).
      time_unfold T_seed_rows. destruct (lrel p); time_simpl; cbn [length];
        unfold karr_seed_factor in *;
        clear -Hrest Hdense Hunit_total Hpositive;
        clearbody work; rewrite !Nat2N.inj_add in *; cbn [N.of_nat] in *; nia.
  Qed.

  (** Flattening source rows counts exactly the stored coefficient occurrences. *)
  Lemma karr_flat_source_length : forall P,
    length (flat_map lhs P) = terms (Reached P).
  Proof.
    intro P. induction P as [|p P IH]; [reflexivity|].
    cbn [flat_map terms rows_of map fold_right]. rewrite length_app, IH. reflexivity.
  Qed.

  (** Flattening transfers common source widths to every raw coefficient occurrence. *)
  Lemma karr_flat_source_sizes : forall P keys bits,
    Forall (fun r => C.row_key_bits r <= keys /\ C.row_bits r <= bits) P ->
    Forall (fun p => Pos.size_nat (X.encode (fst p)) <= keys /\
      Z.size_nat (snd p) <= bits) (flat_map lhs P).
  Proof.
    intros P keys bits Hrows. apply Forall_forall. intros p Hin.
    apply in_flat_map in Hin as [r [Hr Hp]].
    destruct (proj1 (Forall_forall _ _) Hrows r Hr) as [Hkey Hbits].
    pose proof (karr_row_key_member r p Hp).
    pose proof (karr_row_entry_bits r p Hp). split; lia.
  Qed.

  (** Source flattening visits row headers and copies each occurrence once. *)
  Lemma T_karr_flat_source_bounded : forall P,
    (List.T_flat_map (@lhs X.t) (@T_lhs X.t) P <=
      4 * N.of_nat (terms (Reached P) + length P + 1))%N.
  Proof.
    intro P. induction P as [|p P IH].
    - time_unfold List.T_flat_map. cbn [terms rows_of map fold_right length]. lia.
    - pose proof (Datatypes.T_app_le (lhs p) (flat_map lhs P)) as Happ.
      time_unfold List.T_flat_map. time_simpl.
      change (terms (Reached (p :: P))) with (length (lhs p) + terms (Reached P)).
      cbn [length]. rewrite !Nat2N.inj_add in *. cbn [N.of_nat] in *. nia.
  Qed.

  Definition karr_variables_factor : N := (4 * (karr_add_factor + 1) + 64)%N.

  (** Raw coordinate collection has the same logarithmic coefficient-width budget. *)
  Lemma T_karr_variables_raw : forall P keys bits,
    Forall (fun r => C.row_key_bits r <= keys /\ C.row_bits r <= bits) P ->
    (T_variables P <= karr_variables_factor *
      N.of_nat (terms (Reached P) + length P + 1) *
        N.of_nat (keys + bits + Nat.log2 (terms (Reached P)) + 1))%N.
  Proof.
    intros P keys bits Hrows.
    pose proof (karr_flat_source_sizes P keys bits Hrows) as Hsizes.
    assert (Hempty : karr_accum_magnitude PTrieCode.empty (0 * 2 ^ bits)).
    { intros key p Hget. rewrite PTrie.get_empty in Hget. discriminate. }
    pose proof (T_karr_accum_log (flat_map lhs P) PTrieCode.empty keys bits 0
      (terms (Reached P)) Hsizes Hempty ltac:(rewrite karr_flat_source_length; lia)) as Haccum.
    set (tr := fold_left add_term (flat_map lhs P) PTrieCode.empty).
    assert (Hkeys : Forall (fun p => Pos.size_nat (X.encode (fst p)) <= keys)
      (flat_map lhs P)).
    { eapply Forall_impl; [|exact Hsizes]. intros p [Hp _]. exact Hp. }
    pose proof (karr_accum_nodes (flat_map lhs P) PTrieCode.empty keys Hkeys) as Hnodes.
    change (PTrie.nodes tr <= length (flat_map lhs P) * keys) in Hnodes.
    rewrite karr_flat_source_length in Hnodes, Haccum.
    pose proof (T_karr_values_bounded (X.t * Z) tr) as Hvalues.
    pose proof (karr_values_length (X.t * Z) tr) as Hlength.
    pose proof (T_karr_flat_source_bounded P) as Hflat.
    assert (Hmap : (ListDef.T_map (@fst X.t Z) (@Datatypes.T_fst X.t Z) (karr_values tr) <=
      2 * N.of_nat (length (karr_values tr)) + 1)%N).
    { change (ListDef.T_map (@fst X.t Z) (@Datatypes.T_fst X.t Z) (karr_values tr) <=
        (1 + 1) * N.of_nat (length (karr_values tr)) + 1)%N.
      apply karr_T_map_members. intros [x z] _. time_unfold (@Datatypes.T_fst). lia. }
    set (mass := terms (Reached P) + length P + 1).
    set (width := keys + bits + Nat.log2 (terms (Reached P)) + 1).
    set (work := N.of_nat (mass * width)).
    assert (Hwidth : 1 <= width) by (unfold width; lia).
    assert (Hmass : 1 <= mass) by (unfold mass; lia).
    assert (Hpositive : (1 <= work)%N).
    { unfold work. clear -Hwidth Hmass. nia. }
    assert (Hheaders : mass <= mass * width) by (clear -Hwidth mass; nia).
    assert (Hnodes_total : PTrie.nodes tr + 1 <= mass * width).
    { unfold mass, width. clear -Hnodes bits. nia. }
    assert (Hfold_product :
      (N.of_nat (terms (Reached P)) *
        N.of_nat (keys + 2 * bits + Nat.log2 (terms (Reached P)) + 2) <=
        2 * work)%N).
    { assert (Hcount : (N.of_nat (terms (Reached P)) <= N.of_nat mass)%N)
        by (unfold mass; lia).
      assert (Hdouble :
        (N.of_nat (keys + 2 * bits + Nat.log2 (terms (Reached P)) + 2) <=
          2 * N.of_nat width)%N).
      { replace (2 * N.of_nat width)%N with (N.of_nat (2 * width))
          by (rewrite Nat2N.inj_mul; reflexivity). unfold width. lia. }
      replace (2 * work)%N with (N.of_nat mass * (2 * N.of_nat width))%N
        by (unfold work; rewrite Nat2N.inj_mul; ring).
      now apply N.mul_le_mono. }
    assert (Haccum_total :
      (List.T_fold_left add_term T_add_term (flat_map lhs P) PTrieCode.empty <=
        2 * (karr_add_factor + 1) * work + 1)%N).
    { eapply N.le_trans; [exact Haccum|]. apply N.add_le_mono_r.
      replace ((karr_add_factor + 1) * N.of_nat (terms (Reached P)) *
        N.of_nat (keys + 2 * bits + Nat.log2 (terms (Reached P)) + 2))%N with
        ((karr_add_factor + 1) * (N.of_nat (terms (Reached P)) *
          N.of_nat (keys + 2 * bits + Nat.log2 (terms (Reached P)) + 2)))%N by ring.
      replace (2 * (karr_add_factor + 1) * work)%N with
        ((karr_add_factor + 1) * (2 * work))%N by ring.
      now apply N.mul_le_mono_l. }
    assert (Hvalues_total : (T_karr_values tr <= 4 * work)%N).
    { eapply N.le_trans; [exact Hvalues|]. apply N.mul_le_mono_l. unfold work. lia. }
    assert (Hmap_total :
      (ListDef.T_map (@fst X.t Z) (@Datatypes.T_fst X.t Z) (karr_values tr) <=
        3 * work)%N).
    { assert (Hcount : (N.of_nat (length (karr_values tr)) <= work)%N)
        by (unfold work; lia).
      clear -Hmap Hcount Hpositive. nia. }
    assert (Hflat_total : (List.T_flat_map (@lhs X.t) (@T_lhs X.t) P <= 4 * work)%N).
    { eapply N.le_trans; [exact Hflat|]. apply N.mul_le_mono_l.
      change (N.of_nat mass <= work)%N. unfold work. lia. }
    replace (karr_variables_factor * N.of_nat (terms (Reached P) + length P + 1) *
      N.of_nat (keys + bits + Nat.log2 (terms (Reached P)) + 1))%N with
      (karr_variables_factor * work)%N
      by (unfold work, mass, width; rewrite Nat2N.inj_mul; ring).
    time_unfold T_variables. fold tr. time_simpl.
    change (fun (m : ptrie (X.t * Z)) (p : X.t * Z) => T_add_term m p) with T_add_term.
    change (fun _ : lcons X.t => 1%N) with (@T_lhs X.t).
    change (fun _ : X.t * Z => 1%N) with (@Datatypes.T_fst X.t Z).
    replace (karr_variables_factor * N.of_nat mass * N.of_nat width)%N with
      (karr_variables_factor * work)%N by (unfold work; rewrite Nat2N.inj_mul; ring).
    unfold karr_variables_factor.
    clear -Haccum_total Hvalues_total Hmap_total Hflat_total Hpositive.
    clearbody work. nia.
  Qed.

  (** The matrix clock uses a fourth-degree dimension envelope and quadratic bit width. *)
  Definition karr_havoc_volume (dim bits : nat) : nat := (dim + 1)^4 * (bits + 1)^2.

  (** Every positive base increases when its natural exponent increases. *)
  Lemma karr_positive_power_monotone : forall a p q,
    1 <= a -> p <= q -> a^p <= a^q.
  Proof.
    intros a p q Hpositive Horder. apply Nat.pow_le_mono_r; lia.
  Qed.

  (** A coordinate-width product is included in the common matrix envelope. *)
  Lemma karr_havoc_product_volume : forall dim bits,
    (dim + 1) * (bits + 1) <= karr_havoc_volume dim bits.
  Proof.
    intros dim bits. unfold karr_havoc_volume. apply Nat.mul_le_mono.
    - replace (dim + 1) with ((dim + 1)^1) at 1 by (cbn [Nat.pow]; ring).
      apply karr_positive_power_monotone; lia.
    - replace (bits + 1) with ((bits + 1)^1) at 1 by (cbn [Nat.pow]; ring).
      apply karr_positive_power_monotone; lia.
  Qed.

  (** The common matrix volume covers either linear dimension or bit width. *)
  Lemma karr_havoc_volume_lower : forall dim bits,
    dim + 1 <= karr_havoc_volume dim bits /\ bits + 1 <= karr_havoc_volume dim bits.
  Proof.
    intros dim bits. pose proof (karr_havoc_product_volume dim bits) as Hproduct.
    split.
    - eapply Nat.le_trans; [|exact Hproduct]. nia.
    - eapply Nat.le_trans; [|exact Hproduct]. nia.
  Qed.

  (** Dense seeding fits the fourth-degree matrix envelope even when bit width is small. *)
  Lemma karr_havoc_seed_volume : forall dim bits,
    (dim + 1)^3 * (bits + dim + 1) <= karr_havoc_volume dim bits.
  Proof.
    intros dim bits. unfold karr_havoc_volume.
    eapply Nat.le_trans with (m := (dim + 1)^3 * ((dim + 1) * (bits + 1))).
    - apply Nat.mul_le_mono_l. nia.
    - replace ((dim + 1)^3 * ((dim + 1) * (bits + 1))) with
        ((dim + 1)^4 * (bits + 1)) by (cbn [Nat.pow]; ring).
      apply Nat.mul_le_mono_l.
      replace (bits + 1) with ((bits + 1)^1) at 1 by (cbn [Nat.pow]; ring).
      apply karr_positive_power_monotone; lia.
  Qed.

  (** One elimination column fits the same volume with a factor two. *)
  Lemma karr_havoc_step_volume : forall count dim bits,
    count <= dim ->
    (count + 1) * (dim + dim + 1) * (bits + 1)^2 <=
      2 * karr_havoc_volume dim bits.
  Proof.
    intros count dim bits Hcount. unfold karr_havoc_volume.
    replace (2 * ((dim + 1)^4 * (bits + 1)^2)) with
      ((2 * (dim + 1)^4) * (bits + 1)^2) by (cbn [Nat.pow]; ring).
    apply Nat.mul_le_mono_r.
    eapply Nat.le_trans with (m := (dim + 1) * (2 * (dim + 1))).
    - apply Nat.mul_le_mono; lia.
    - replace ((dim + 1) * (2 * (dim + 1))) with (2 * (dim + 1)^2) by (cbn [Nat.pow]; ring).
      apply Nat.mul_le_mono_l. apply karr_positive_power_monotone; lia.
  Qed.

  (** Visiting at most one output per source row fits the common matrix envelope. *)
  Lemma karr_havoc_rows_volume : forall count dim bits,
    count <= dim ->
    (count + 1) * (dim + 1)^2 * (bits + 1)^2 <= karr_havoc_volume dim bits.
  Proof.
    intros count dim bits Hcount. unfold karr_havoc_volume. apply Nat.mul_le_mono_r.
    eapply Nat.le_trans with (m := (dim + 1) * (dim + 1)^2).
    - apply Nat.mul_le_mono_r. lia.
    - replace ((dim + 1) * (dim + 1)^2) with ((dim + 1)^3) by (cbn [Nat.pow]; ring).
      apply karr_positive_power_monotone; lia.
  Qed.

  (** The abstract certificate checker fits the one-column matrix volume. *)
  Lemma karr_havoc_checker_measure : forall P ms c dim bits,
    length P <= dim -> length ms <= dim ->
    Forall (fun r => length (lhs r) <= dim /\
      C.row_key_bits r <= bits /\ C.row_bits r <= bits) P ->
    Forall (fun m => Z.size_nat m <= bits) ms ->
    length (lhs c) <= dim -> C.row_key_bits c <= bits -> C.row_bits c <= bits ->
    Nat.log2 (length P) <= bits ->
    C.csize P ms + 2 * (C.lsize c + C.cbits P ms + 1) <=
      32 * karr_havoc_volume dim bits.
  Proof.
    intros P ms c dim bits Hrows_len Hmult_len Hrows Hmult
      Hclen Hckeys Hcbits Hlog.
    pose proof (karr_csize_envelope P ms dim bits bits bits Hrows Hmult) as Hsize.
    assert (Hrow_bits : Forall (fun r => C.row_bits r <= bits) P).
    { eapply Forall_impl; [|exact Hrows]. intros r [_ [_ Hr]]. exact Hr. }
    pose proof (karr_cbits_envelope P ms bits bits Hrow_bits Hmult) as Hbits.
    pose proof (karr_lsize_envelope c dim bits bits Hclen Hckeys Hcbits) as Hline.
    pose proof (karr_havoc_rows_volume 0 dim bits ltac:(lia)) as Hsquare.
    pose proof (karr_havoc_product_volume dim bits) as Hproduct.
    pose proof (karr_havoc_volume_lower dim bits) as [_ Hwidth].
    assert (Hfactor : bits + (bits + 1) * (bits + 1) + 1 <=
      2 * (bits + 1)^2) by (rewrite Nat.pow_2_r; nia).
    assert (Hsize_bound : C.csize P ms <= 4 * karr_havoc_volume dim bits).
    { eapply Nat.le_trans; [exact Hsize|].
      eapply Nat.le_trans with (m :=
        2 * (dim + 1) * (dim + 1) * (2 * (bits + 1)^2)).
      - apply Nat.mul_le_mono; [apply Nat.mul_le_mono; lia|exact Hfactor].
      - replace (2 * (dim + 1) * (dim + 1) * (2 * (bits + 1)^2))
          with (4 * ((dim + 1)^2 * (bits + 1)^2))
          by (rewrite !Nat.pow_2_r; ring).
        lia. }
    assert (Hline_bound : C.lsize c <= 2 * karr_havoc_volume dim bits).
    { eapply Nat.le_trans; [exact Hline|].
      eapply Nat.le_trans with (m := (dim + 1) * (2 * (bits + 1))).
      - apply Nat.mul_le_mono_l. lia.
      - replace ((dim + 1) * (2 * (bits + 1)))
          with (2 * ((dim + 1) * (bits + 1))) by ring.
        lia. }
    assert (Hbits_bound : C.cbits P ms <= 3 * karr_havoc_volume dim bits)
      by lia.
    lia.
  Qed.

  (** Raw row headers are paid by the matrix budget in addition to occurrence preparation. *)
  Lemma karr_havoc_preparation_volume : forall total count width dim bits,
    count <= dim -> width <= bits + 1 ->
    (total + count + 1) * width <=
      total * (width + 1) + karr_havoc_volume dim bits.
  Proof.
    intros total count width dim bits Hcount Hwidth.
    assert (Hheaders : (count + 1) * width <= karr_havoc_volume dim bits).
    { eapply Nat.le_trans; [|apply karr_havoc_product_volume].
      apply Nat.mul_le_mono; lia. }
    nia.
  Qed.

  (** The frozen cubic-Hadamard havoc budget dominates the local one-column volume. *)
  Lemma karr_havoc_volume_public : forall dim bits,
    1 <= dim ->
    karr_havoc_volume dim bits <= 16 * (dim^3 * (ellB dim bits + 1)^2).
  Proof.
    intros dim bits Hpositive. unfold karr_havoc_volume.
    assert (Hdimension : (dim + 1)^4 <= 16 * dim^4).
    { replace (16 * dim^4) with ((2 * dim)^4) by (cbn [Nat.pow]; ring).
      apply Nat.pow_le_mono_l. lia. }
    assert (Hwidth : dim * (bits + 1) <= ellB dim bits + 1).
    { unfold ellB. nia. }
    assert (Hwidth_square : (dim * (bits + 1))^2 <= (ellB dim bits + 1)^2).
    { now apply Nat.pow_le_mono_l. }
    eapply Nat.le_trans with (m := 16 * dim^4 * (bits + 1)^2).
    - now apply Nat.mul_le_mono_r.
    - eapply Nat.le_trans with (m := 16 * (dim^3 * (dim * (bits + 1))^2)).
      + replace (16 * dim^4 * (bits + 1)^2) with
          (16 * (dim^4 * (bits + 1)^2)) by (cbn [Nat.pow]; ring).
        replace (16 * (dim^3 * (dim * (bits + 1))^2)) with
          (16 * (dim^5 * (bits + 1)^2)) by (cbn [Nat.pow]; ring).
        apply Nat.mul_le_mono_l, Nat.mul_le_mono_r.
        apply karr_positive_power_monotone; lia.
      + apply Nat.mul_le_mono_l, Nat.mul_le_mono_l. exact Hwidth_square.
  Qed.

  (** Assignment includes the form's raw occurrences in its matrix dimension. *)
  Definition karr_assign_dim (f : lin X.t) (P : list (lcons X.t)) : nat :=
    n (Reached P) + length (coef f) + 1.

  (** Assignment adds the selected key and form widths to the prepared source width. *)
  Definition karr_assign_bits (x : X.t) (f : lin X.t) (P : list (lcons X.t)) : nat :=
    nell (Reached P) + X.bits x + F.form_bits f.

  (** The shared affine assignment budget pays raw preparation and its bounded matrix work. *)
  Definition karr_assign_budget (x : X.t) (f : lin X.t) (P : list (lcons X.t)) : nat :=
    terms (Reached P) * (nell (Reached P) + 1) +
      karr_havoc_volume (karr_assign_dim f P) (karr_assign_bits x f P).

  (** The frozen numeric polynomial grows with both matrix dimension and entry width. *)
  Lemma karr_numeric_polynomial_mono : forall dim dim' bits bits',
    dim <= dim' -> bits <= bits' ->
    dim^3 * (ellB dim bits + 1)^2 <= dim'^3 * (ellB dim' bits' + 1)^2.
  Proof.
    intros dim dim' bits bits' Hdim Hbits. apply Nat.mul_le_mono.
    - now apply Nat.pow_le_mono_l.
    - apply Nat.pow_le_mono_l.
      assert (Hwidth : ellB dim bits <= ellB dim' bits').
      { unfold ellB. apply Nat.mul_le_mono; [exact Hdim|].
        pose proof (Nat.log2_le_mono dim dim' Hdim). lia. }
      lia.
  Qed.

  (** The private affine assignment budget fits the frozen term and bit-size allowance. *)
  Lemma karr_assign_budget_public : forall x f P e,
    length (coef f) <= tsize e -> F.form_bits f <= F.bits_e e ->
    karr_assign_budget x f P <= 16 * assign_work x e (Reached P).
  Proof.
    intros x f P e Hlength Hbits.
    pose proof (karr_havoc_volume_public (karr_assign_dim f P)
      (karr_assign_bits x f P) ltac:(unfold karr_assign_dim; lia)) as Hvolume.
    pose proof (karr_numeric_polynomial_mono
      (karr_assign_dim f P) (n (Reached P) + tsize e + 1)
      (karr_assign_bits x f P) (nell (Reached P) + X.bits x + F.bits_e e)
      ltac:(unfold karr_assign_dim; lia)
      ltac:(unfold karr_assign_bits; lia)) as Hpolynomial.
    unfold karr_assign_budget, assign_work. lia.
  Qed.

  (** The assignment allowance also pays the havoc used for unknown or wrapped forms. *)
  Lemma karr_assign_havoc_budget : forall x e s,
    havoc_work x s <= assign_work x e s.
  Proof.
    intros x e s.
    pose proof (karr_numeric_polynomial_mono
      (n s + 1) (n s + tsize e + 1)
      (nell s + X.bits x) (nell s + X.bits x + F.bits_e e)
      ltac:(lia) ltac:(lia)) as Hpolynomial.
    unfold havoc_work, assign_work. lia.
  Qed.

  (** Completed row and havoc bounds lift through the exact linearizer dispatch clock. *)
  Lemma T_karr_assign_from_rows : forall row_factor havoc_factor,
    (forall x f P, (T_assign_rows x f P <=
      row_factor * N.of_nat (karr_assign_budget x f P))%N) ->
    (forall x s, (T_havoc x s <=
      havoc_factor * N.of_nat (havoc_work x s + 1))%N) ->
    forall x e s, (T_assign x e s <= (16 * row_factor + havoc_factor + 32) *
      N.of_nat (assign_work x e s + 1))%N.
  Proof.
    intros row_factor havoc_factor Hrows Hhavoc x e [|P].
    - time_unfold T_assign. time_simpl.
      assert (Hpositive : (1 <= N.of_nat (assign_work x e Unreached + 1))%N) by lia.
      nia.
    - set (work := N.of_nat (assign_work x e (Reached P) + 1)).
      assert (Hpositive : (1 <= work)%N) by (unfold work; lia).
      assert (Hlin_clock : (F.T_lin_of e <= work)%N).
      { unfold work, assign_work. rewrite !Nat2N.inj_add, N2Nat.id. lia. }
      assert (Hhavoc_total : (T_havoc x (Reached P) <= havoc_factor * work)%N).
      { eapply N.le_trans; [apply Hhavoc|]. apply N.mul_le_mono_l.
        pose proof (karr_assign_havoc_budget x e (Reached P)) as Hbudget.
        unfold work. clear -Hbudget. lia. }
      time_unfold T_assign.
      destruct (F.lin_of e) as [[f wrapping]|] eqn:Hlin; time_simpl.
      + destruct wrapping; time_simpl.
        * destruct (F.lin_of_size _ _ _ Hlin) as [Hlength Hbits].
          cbn [F.wrap_bits] in Hbits.
          pose proof (karr_assign_budget_public x f P e Hlength ltac:(lia)) as Hbudget.
          assert (Hcast : (N.of_nat (karr_assign_budget x f P) <= 16 * work)%N).
          { unfold work. replace (16 * N.of_nat (assign_work x e (Reached P) + 1))%N
              with (N.of_nat (16 * (assign_work x e (Reached P) + 1)))
              by (rewrite Nat2N.inj_mul; reflexivity).
            clear -Hbudget. lia. }
          assert (Hrows_total : (T_assign_rows x f P <= 16 * row_factor * work)%N).
          { eapply N.le_trans; [apply Hrows|].
            replace (16 * row_factor * work)%N with (row_factor * (16 * work))%N
              by ring. now apply N.mul_le_mono_l. }
          fold work. clear -Hrows_total Hlin_clock Hpositive. clearbody work. nia.
        * fold work. clear -Hhavoc_total Hlin_clock Hpositive. clearbody work. nia.
      + fold work. clear -Hhavoc_total Hlin_clock Hpositive. clearbody work. nia.
  Qed.

  Definition c_lat : N := 1. (* STUB *)
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof.
    unfold c_lat. lia.
  Qed.
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
  Definition c_num : N := (karr_assume_factor + 1)%N.
  Lemma T_assign_le : forall x e s,
    (T_assign x e s <= c_num * N.of_nat (assign_work x e s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_havoc_le : forall x s,
    (T_havoc x s <= c_num * N.of_nat (havoc_work x s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_assume_le : forall g es s,
    (T_assume g es s <= c_num * N.of_nat (assume_work g es s + 1))%N.
  Proof.
    intros g es s. eapply N.le_trans; [apply T_karr_assume_bounded|].
    apply N.mul_le_mono_r. unfold c_num. lia.
  Qed.
  Lemma T_narrow_le : forall a b,
    (T_narrow a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. time_unfold T_narrow. unfold c_lat. lia.
  Qed.
  Lemma T_range_le : forall e s, (T_range e s <= c_num * N.of_nat (range_work e s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma range_size : forall e s,
    (N.of_nat
      (match fst (range e s) with Fin z => Z.size_nat z | _ => 0 end +
       match snd (range e s) with Fin z => Z.size_nat z | _ => 0 end) <=
     c_num * N.of_nat (range_bits e s + 1))%N.
  Proof. Admitted. (* STUB *)
  Definition c_karr : N := (karr_subst_factor + 1)%N.
  Lemma T_subst_le : forall x f r,
    (T_subst x f r <= c_karr * N.of_nat
      ((X.bits x + C.lsize (LCons _ (coef f) REq (cst f)) + C.lsize r + 1)^2))%N.
  Proof.
    intros x f r. eapply N.le_trans; [apply T_karr_subst_bounded|].
    apply N.mul_le_mono_r. unfold c_karr. lia.
  Qed.
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

  (** Every key retained by pairing belongs to the original coordinate list. *)
  Lemma combine_keys_in : forall (xs : list X.t) (zs : list Z) x,
    In x (map fst (List.combine xs zs)) -> In x xs.
  Proof.
    intro xs. induction xs as [|y xs IH]; intros [|z zs] x Hin;
      cbn [List.combine map fst In] in *; try contradiction.
    destruct Hin as [Hsame|Hin]; [now left|]. right. now apply IH with (zs := zs).
  Qed.

  (** Pairing distinct coordinates with a coefficient vector retains distinct keys. *)
  Lemma combine_keys_nodup : forall (xs : list X.t) (zs : list Z),
    NoDup xs -> NoDup (map fst (List.combine xs zs)).
  Proof.
    intro xs. induction xs as [|x xs IH]; intros [|z zs] Hunique;
      cbn [List.combine map fst]; try solve [constructor].
    inversion Hunique as [|key keys Hnot Htail]; subst key keys.
    constructor.
    - intro Hin. apply Hnot. now apply combine_keys_in with (zs := zs).
    - now apply IH.
  Qed.

  (** Dropping zero coefficients from a unique coordinate list preserves unique keys. *)
  Lemma sparse_nodup : forall xs zs,
    NoDup xs -> NoDup (map fst (sparse xs zs)).
  Proof.
    intros xs zs Hunique. unfold sparse. apply karr_nodup_map_filter.
    now apply combine_keys_nodup.
  Qed.

  (** Normalization gives every source row a unique coefficient at each key. *)
  Lemma normal_normalize_rows : forall P, normal (map normalize_row P).
  Proof.
    intro P. unfold normal. apply Forall_map. apply Forall_forall. intros r _.
    cbn [normalize_row lhs]. apply normalize_coef_nodup.
  Qed.

  (** Every affine-hull output has distinct coefficient keys, even for raw inputs. *)
  Lemma normal_affine_hull : forall a b, normal (affine_hull a b).
  Proof.
    intros a b. unfold normal, affine_hull. apply present_forall.
    intros r c Hrow. rewrite (checked_hull_row_shape _ _ _ _ _ Hrow).
    cbn [lhs]. apply sparse_nodup. apply variables_nodup.
  Qed.

  (** A successful projection extractor returns its sparse equality row unchanged. *)
  Lemma projected_row_shape : forall x xs P r c,
    projected_row x xs P r = Some c ->
    c = LCons X.t (sparse xs (kcoeff r)) REq (kright r).
  Proof.
    intros x xs P r c Hrow. unfold projected_row in Hrow.
    remember (LCons X.t (sparse xs (kcoeff r)) REq (kright r)) as candidate
      eqn:Hcandidate in Hrow.
    destruct (negb (mentions x candidate) &&
      C.check_entails P candidate (Cert (kweight r) 1 false)); [|discriminate].
    injection Hrow as Hsame. subst c. exact Hcandidate.
  Qed.

  (** Moving the eliminated variable to the front preserves unique coordinates. *)
  Lemma project_variables_nodup : forall x P,
    NoDup (x :: filter (fun y => negb (X.eqb y x)) (variables P)).
  Proof.
    intros x P. constructor.
    - intro Hin. apply filter_In in Hin as [_ Hkeep].
      rewrite key_eqb_refl in Hkeep. discriminate.
    - apply NoDup_filter. apply variables_nodup.
  Qed.

  (** Projection normalizes both its equality basis and its retained inequalities. *)
  Lemma normal_project : forall x P, normal (project x P).
  Proof.
    intros x P. unfold normal, project. apply Forall_app. split.
    - apply present_forall. intros r c Hrow.
      rewrite (projected_row_shape _ _ _ _ _ Hrow). cbn [lhs].
      apply sparse_nodup. apply project_variables_nodup.
    - apply Forall_forall. intros r Hin. apply filter_In in Hin as [Hin _].
      apply in_map_iff in Hin as [s [Hsame _]]. subst r.
      cbn [normalize_row lhs]. apply normalize_coef_nodup.
  Qed.

  (** Normalization does not change which source multipliers are equality-only. *)
  Lemma equality_weights_normalized : forall P ms,
    equality_weights P ms -> equality_weights (map normalize_row P) ms.
  Proof.
    intros P ms Hweights. induction Hweights as [|p m P ms Hhead Htail IH].
    - constructor.
    - cbn [map]. constructor; [exact Hhead | exact IH].
  Qed.

  (** Merged duplicate keys preserve the exact weighted coefficient sum. *)
  Lemma comb_coef_normalized : forall P ms x,
    C.comb_coef (map normalize_row P) ms x = C.comb_coef P ms x.
  Proof.
    intro P. induction P as [|p P IH]; intros [|m ms] x; try reflexivity.
    change ((m * coefficient x (normalize_coef (lhs p)) +
      C.comb_coef (map normalize_row P) ms x)%Z =
      (m * coefficient x (lhs p) + C.comb_coef P ms x)%Z).
    rewrite normalize_coef_coefficient, IH. reflexivity.
  Qed.

  (** Preparing coefficient lists leaves the weighted right-hand side unchanged. *)
  Lemma comb_rhs_normalized : forall P ms,
    C.comb_rhs (map normalize_row P) ms = C.comb_rhs P ms.
  Proof.
    intro P. induction P as [|p P IH]; intros [|m ms]; try reflexivity.
    change ((m * rhs p + C.comb_rhs (map normalize_row P) ms)%Z =
      (m * rhs p + C.comb_rhs P ms)%Z). now rewrite IH.
  Qed.

  (** Every exact equality certificate is also exact for the normalized source. *)
  Lemma equality_certificate_normalized : forall P c ms sc,
    equality_certificate P c ms sc ->
    equality_certificate (map normalize_row P) c ms sc.
  Proof.
    intros P c ms sc [Hweights [Hscale [Hcoef Hrhs]]].
    split; [now apply equality_weights_normalized |]. split; [exact Hscale |].
    split.
    - intro x. rewrite comb_coef_normalized. exact (Hcoef x).
    - rewrite comb_rhs_normalized. exact Hrhs.
  Qed.

  (** Sparse reconstruction of a tracked source row has an exact scale-one certificate. *)
  Lemma row_tracks_sparse_certificate : forall P xs target r,
    NoDup xs ->
    (forall s, In s P -> forall x z, In (x, z) (lhs s) -> In x xs) ->
    row_tracks P xs target 0 r -> kscale r = 0%Z ->
    equality_certificate P (LCons X.t (sparse xs (kcoeff r)) REq (kright r))
      (kweight r) 1.
  Proof.
    intros P xs target r Hunique Hsupport [Hweights [Hcoords Hrhs]] Hscale.
    rewrite Hscale in Hcoords, Hrhs. cbn [repeat app] in Hcoords.
    assert (Hcoeffs : kcoeff r = map (C.comb_coef P (kweight r)) xs).
    { rewrite Hcoords. apply map_ext. intro y. ring. }
    split; [exact Hweights |]. split; [lia |]. split.
    - intro x. change (C.comb_coef P (kweight r) x =
        (1 * coefficient x (sparse xs (kcoeff r)))%Z).
      rewrite Z.mul_1_l, Hcoeffs. unfold sparse.
      rewrite coefficient_nonzero, combine_coordinate_map.
      assert (Hdec : {In x xs} + {~ In x xs}).
      { apply in_dec. intros a b. destruct (X.eqb_spec a b); auto. }
      destruct Hdec as [Hin | Habsent].
      + symmetry. now apply coefficient_coordinates.
      + rewrite coefficient_absent.
        * apply comb_coef_zero. intros s Hs. apply coefficient_absent. intro Hin.
          apply in_map_iff in Hin as [[y z] [Hsame Hin]]. cbn [fst] in Hsame.
          subst y. apply Habsent. exact (Hsupport s Hs x z Hin).
        * rewrite map_map. change (~ In x (map (fun y => y) xs)).
          now rewrite map_id.
    - cbn [lrel rhs]. lia.
  Qed.

  (** Raw projection coordinates contain every source occurrence, including canceled keys. *)
  Lemma project_variables_contains : forall x P r y z,
    In r P -> In (y, z) (lhs r) ->
    In y (x :: filter (fun q => negb (X.eqb q x)) (variables P)).
  Proof.
    intros x P r y z Hr Hz. destruct (X.eqb_spec y x) as [Hequal | Hother].
    - subst y. now left.
    - right. apply filter_In. split.
      + now apply variables_contains with (r := r) (z := z).
      + apply negb_true_iff. destruct (X.eqb_spec y x); congruence.
  Qed.

  (** Every row produced by one-column elimination has the advertised exact source sum. *)
  Lemma project_basis_certificate : forall x P r,
    let xs := x :: filter (fun y => negb (X.eqb y x)) (variables P) in
    In r (karr_bareiss 1 1 (seed_rows xs (length P) 0 (map normalize_row P))) ->
    equality_certificate P (LCons X.t (sparse xs (kcoeff r)) REq (kright r))
      (kweight r) 1.
  Proof.
    intros x P r xs Hin.
    apply row_tracks_sparse_certificate with (target := LCons X.t [] REq 0).
    - apply project_variables_nodup.
    - intros s Hs y z Hz. now apply project_variables_contains with (r := s) (z := z).
    - apply (proj1 (Forall_forall _ _)
        (bareiss_tracks 1 P xs (LCons X.t [] REq 0) 0 1
          (seed_rows xs (length P) 0 (map normalize_row P))
          ltac:(unfold xs; cbn [length]; lia) (seed_rows_tracks _ _ _)) r Hin).
    - apply (proj1 (Forall_forall _ _)
        (bareiss_scale_zero 1 1 (seed_rows xs (length P) 0 (map normalize_row P))
          (seed_rows_scale_zero _ _ _ _)) r Hin).
  Qed.

  (** Preparing the checker source preserves the former projection result exactly. *)
  Lemma project_raw_source_agrees : forall x P,
    project x P =
      let xs := x :: filter (fun y => negb (X.eqb y x)) (variables P) in
      let rows := karr_bareiss 1 1 (seed_rows xs (length P) 0 (map normalize_row P)) in
      present (map (projected_row x xs P) rows) ++
        filter (fun r => match lrel r with
          | REq => false | RLe => negb (mentions x r) end) (map normalize_row P).
  Proof.
    intros x P. unfold project. f_equal. f_equal.
    apply map_ext_in. intros r Hin.
    pose proof (project_basis_certificate x P r Hin) as Hcertificate.
    pose proof (equality_certificate_checked _ _ _ _ Hcertificate) as Hraw.
    pose proof (equality_certificate_checked _ _ _ _
      (equality_certificate_normalized _ _ _ _ Hcertificate)) as Hnormal.
    unfold projected_row. rewrite Hraw, Hnormal. reflexivity.
  Qed.

  (** Both affine assignment branches construct only normalized rows. *)
  Lemma normal_assign_rows : forall x f P, normal (assign_rows x f P).
  Proof.
    intros x f P. unfold assign_rows.
    destruct (Z.eqb (coefficient x (coef f)) 0).
    - constructor.
      + cbn [normalize_row lhs]. apply normalize_coef_nodup.
      + apply normal_project.
    - unfold normal. apply Forall_map. apply Forall_forall. intros r _.
      cbn [inverse_row normalize_row lhs]. apply normalize_coef_nodup.
  Qed.

  (** Every emitted equality atom has merged duplicate keys. *)
  Lemma normal_atom_rows : forall a, normal (atom_rows a).
  Proof.
    intros [fl wl comparison fr wr].
    destruct wl, wr, comparison; cbn [normal atom_rows al alw ar arw acmp];
      try solve [constructor].
    constructor; [|constructor]. cbn [normalize_row lhs]. apply normalize_coef_nodup.
  Qed.

  (** Top has no repeated coefficients. *)
  Lemma normal_top : normal_s top.
  Proof.
    constructor.
  Qed.
  (** Join keeps rows free of repeated keys. *)
  Lemma normal_join : forall a b, normal_s a -> normal_s b -> normal_s (join a b).
  Proof.
    intros [|P] [|Q] Ha Hb; [exact I|exact Hb|exact Ha|].
    apply normal_affine_hull.
  Qed.
  (** Widening keeps rows free of repeated keys. *)
  Lemma normal_widen : forall p a b,
    normal_s a -> normal_s b -> normal_s (widen p a b).
  Proof.
    intros p a b Ha Hb. unfold widen. destruct (leb b a); [exact Ha|].
    now apply normal_join.
  Qed.
  (** Narrowing keeps rows free of repeated keys. *)
  Lemma normal_narrow : forall a b, normal_s a -> normal_s b -> normal_s (narrow a b).
  Proof.
    intros a b _ Hb. exact Hb.
  Qed.
  (** Assignment normalizes its new rows. *)
  Lemma normal_assign : forall x e s, normal_s s -> normal_s (assign x e s).
  Proof.
    intros x e [|P] _; [exact I|]. unfold assign.
    destruct (F.lin_of e) as [[f wrapping]|]; [destruct wrapping|].
    - apply normal_assign_rows.
    - apply normal_project.
    - apply normal_project.
  Qed.
  (** Havoc keeps rows free of repeated keys. *)
  Lemma normal_havoc : forall x s, normal_s s -> normal_s (havoc x s).
  Proof.
    intros x [|P] _; [exact I|]. apply normal_project.
  Qed.
  (** Assumption normalizes the rows it adds. *)
  Lemma normal_assume : forall g es s, normal_s s -> normal_s (assume g es s).
  Proof.
    intros g es [|P] _; [exact I|].
    change (normal (flat_map atom_rows (F.atoms_of g es) ++ map normalize_row P)).
    unfold normal. apply Forall_app. split.
    - apply Forall_forall. intros r Hin. apply in_flat_map in Hin as [a [_ Hr]].
      exact (proj1 (Forall_forall _ _) (normal_atom_rows a) r Hr).
    - apply normal_normalize_rows.
  Qed.
  (** This widening has no repeated threshold search. *)
  Lemma F_wunits : forall s, wunits s = 0.
  Proof.
    reflexivity.
  Qed.
  Definition echelon (P : list (lcons X.t)) : Prop :=
    Forall (fun r => lrel r = REq) P /\
    (forall i r, nth_error P i = Some r -> exists x a, In (x, a) (lhs r) /\ a <> 0%Z /\
      forall j s, nth_error P j = Some s -> i <> j ->
        forall b, In (x, b) (lhs s) -> b = 0%Z).
  (** The augmented source matrix includes the identity certificate columns. *)
  Definition bareiss_seeds (P : list (lcons X.t)) : list karr_row :=
    seed_rows (variables P) (length P) 0 (map normalize_row P).
  TimeFun bareiss_seeds.

  (** Entries are collected from the actual normalized equality-elimination run. *)
  Definition bareiss_entries (P : list (lcons X.t)) : list Z :=
    snd (karr_bareiss_record (length (variables P)) 1 (bareiss_seeds P)).

  (** Input minors use an independent Laplace expansion of the augmented seed matrix. *)
  Definition input_minors (P : list (lcons X.t)) : list Z :=
    karr_signed_minors (length (variables P) + length P + 2)
      (map karr_row_entries (bareiss_seeds P)).
  TimeFun bareiss_entries.
  TimeFun input_minors.

  (** Instrumentation returns the same basis used by contradiction detection. *)
  Lemma bareiss_record_basis : forall P,
    fst (karr_bareiss_record (length (variables P)) 1 (bareiss_seeds P)) =
      equality_basis (variables P) P.
  Proof.
    intro P. apply karr_bareiss_record_value.
  Qed.

  (** Every seed row has coefficient, RHS, multiplier and scale columns of fixed width. *)
  Lemma seed_entries_width : forall xs total index P,
    Forall (fun r => length (karr_row_entries r) = length xs + total + 2)
      (seed_rows xs total index P).
  Proof.
    intros xs total index P. revert index.
    induction P as [|r P IH]; intro index; [constructor|].
    cbn [seed_rows]. destruct (lrel r); [constructor|apply IH].
    - unfold karr_row_entries. cbn [kcoeff kright kweight kscale length].
      rewrite !length_app. cbn [length]. rewrite length_app, karr_unit_length. cbn [length].
      unfold dense. rewrite length_map. lia.
    - apply IH.
  Qed.

  (** The initialized run satisfies the labeled minor law at order zero. *)
  Lemma bareiss_run_state_initial : forall P,
    karr_run_state (length (variables P) + length P + 2)
      (length (variables P))
      (map karr_row_entries (bareiss_seeds P)) 1 [] []
      (seq 0 (length (variables P) + length P + 2))
      (map karr_row_entries (bareiss_seeds P)) (bareiss_seeds P).
  Proof.
    intro P. unfold karr_run_state. repeat (apply conj).
    - lia.
    - reflexivity.
    - now rewrite length_map.
    - unfold bareiss_seeds. apply seed_rows_width.
    - rewrite length_seq. unfold bareiss_seeds. apply seed_entries_width.
    - rewrite length_seq. lia.
    - reflexivity.
    - cbn [app]. apply Permutation_refl.
    - cbn [app]. apply karr_increasing_seq.
    - cbn [app]. replace (length (variables P) + length P + 2) with
        (0 + (length (variables P) + length P + 2)) by lia.
      apply karr_seq_bounded.
    - rewrite karr_combine_self. apply karr_minor_law_initial.
  Qed.

  (** Any coordinate list initializes the same labeled minor invariant. *)
  Lemma karr_run_state_seed : forall xs P,
    karr_run_state (length xs + length P + 2) (length xs)
      (map karr_row_entries (seed_rows xs (length P) 0 (map normalize_row P)))
      1 [] [] (seq 0 (length xs + length P + 2))
      (map karr_row_entries (seed_rows xs (length P) 0 (map normalize_row P)))
      (seed_rows xs (length P) 0 (map normalize_row P)).
  Proof.
    intros xs P. unfold karr_run_state. repeat (apply conj).
    - lia.
    - reflexivity.
    - now rewrite length_map.
    - apply seed_rows_width.
    - rewrite length_seq. apply seed_entries_width.
    - rewrite length_seq. lia.
    - reflexivity.
    - cbn [app]. apply Permutation_refl.
    - cbn [app]. apply karr_increasing_seq.
    - cbn [app]. replace (length xs + length P + 2) with
        (0 + (length xs + length P + 2)) by lia.
      apply karr_seq_bounded.
    - rewrite karr_combine_self. apply karr_minor_law_initial.
  Qed.

  (** Every initialized certificate vector has a zero when two source slots exist. *)
  Lemma seed_rows_zero_weight : forall xs total index P,
    2 <= total ->
    Forall (fun r => In 0%Z (kweight r)) (seed_rows xs total index P).
  Proof.
    intros xs total index P. revert index.
    induction P as [|r P IH]; intros index Htotal; [constructor|].
    cbn [seed_rows]. destruct (lrel r).
    - constructor; [cbn [kweight]; now apply karr_unit_zero|now apply IH].
    - now apply IH.
  Qed.

  (** Every seed row has a literal zero when the input has at least two rows. *)
  Lemma bareiss_seed_zero : forall P r,
    2 <= length P -> In r (bareiss_seeds P) ->
    In 0%Z (karr_row_entries r).
  Proof.
    intros P r Hcount Hin. unfold bareiss_seeds in Hin.
    pose proof (proj1 (Forall_forall _ _)
      (seed_rows_zero_weight (variables P) (length P) 0
        (map normalize_row P) Hcount) r Hin) as Hzero.
    unfold karr_row_entries. apply in_or_app. right. right.
    apply in_or_app. now left.
  Qed.

  (** Any coordinate list keeps a literal zero in a seed with two source slots. *)
  Lemma karr_seed_zero : forall xs P r,
    2 <= length P ->
    In r (seed_rows xs (length P) 0 (map normalize_row P)) ->
    In 0%Z (karr_row_entries r).
  Proof.
    intros xs P r Hcount Hin.
    pose proof (proj1 (Forall_forall _ _)
      (seed_rows_zero_weight xs (length P) 0
        (map normalize_row P) Hcount) r Hin) as Hzero.
    unfold karr_row_entries. apply in_or_app. right. right.
    apply in_or_app. now left.
  Qed.

  (** Every initial augmented entry is both traced and an input minor. *)
  Lemma bareiss_initial_entry : forall P r z,
    In r (bareiss_seeds P) -> In z (karr_row_entries r) ->
    In z (bareiss_entries P) /\ In z (input_minors P).
  Proof.
    intros P r z Hr Hz. split.
    - unfold bareiss_entries. apply karr_bareiss_record_initial.
      apply in_flat_map. now exists r.
    - unfold input_minors. apply karr_signed_minors_entry with (row := karr_row_entries r).
      + now apply in_map.
      + unfold bareiss_seeds in Hr.
        pose proof (proj1 (Forall_forall _ _)
          (seed_entries_width (variables P) (length P) 0 (map normalize_row P)) r Hr) as Hwidth.
        rewrite Hwidth. reflexivity.
      + exact Hz.
  Qed.

  (** A run with two source slots and a live seed has zero among its input minors. *)
  Lemma input_minors_zero : forall P,
    2 <= length P -> bareiss_seeds P <> [] -> In 0%Z (input_minors P).
  Proof.
    intros P Hcount Hnonempty.
    destruct (bareiss_seeds P) as [|r rs] eqn:Hseeds; [contradiction|].
    assert (Hin : In r (bareiss_seeds P)) by (rewrite Hseeds; now left).
    exact (proj2 (bareiss_initial_entry P r 0 Hin
      (bareiss_seed_zero P r Hcount Hin))).
  Qed.

  (** Every final basis entry occurs in the trace. *)
  Lemma bareiss_basis_entry : forall P r z,
    In r (equality_basis (variables P) P) -> In z (karr_row_entries r) ->
    In z (bareiss_entries P).
  Proof.
    intros P r z Hr Hz. unfold bareiss_entries. apply karr_bareiss_record_final.
    apply in_flat_map. exists r. split; [exact Hr|exact Hz].
  Qed.
  Lemma subst_sat : forall v x f r, sat v (subst x f r) <->
    sat (upd X.eqb v x (eval_lin v f)) r.
  Proof.
    exact subst_sat_checked.
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
  (** Integer multiplication multiplies absolute magnitudes exactly. *)
  Lemma karr_magnitude_mul : forall a b,
    karr_magnitude (a * b) = karr_magnitude a * karr_magnitude b.
  Proof.
    intros a b. unfold karr_magnitude. rewrite Z.abs_mul.
    now rewrite Z2Nat.inj_mul by apply Z.abs_nonneg.
  Qed.

  (** Negation leaves absolute magnitude unchanged. *)
  Lemma karr_magnitude_opp : forall z, karr_magnitude (- z) = karr_magnitude z.
  Proof.
    intros [|p|p]; reflexivity.
  Qed.

  (** Either determinant sign has unit absolute magnitude. *)
  Lemma karr_magnitude_sign : forall (negative : bool) z,
    karr_magnitude ((if negative then (-1) else 1) * z) = karr_magnitude z.
  Proof.
    intros [|] z.
    - replace (-1 * z)%Z with (- z)%Z by ring. apply karr_magnitude_opp.
    - now rewrite Z.mul_1_l.
  Qed.

  (** Summing a list of bounded signed values pays one magnitude allowance per entry. *)
  Lemma karr_magnitude_sum : forall xs bound,
    Forall (fun z => karr_magnitude z <= bound) xs ->
    karr_magnitude (fold_right Z.add 0%Z xs) <= length xs * bound.
  Proof.
    intros xs bound Hbound. induction Hbound as [|z zs Hz Htail IH].
    - change (0 <= 0). lia.
    - cbn [fold_right length].
      pose proof (karr_magnitude_add z (fold_right Z.add 0%Z zs)) as Hsum. nia.
  Qed.

  (** Dense out-of-range lookup returns zero and otherwise preserves a common entry width. *)
  Lemma karr_nth_bits : forall index row bits,
    Forall (fun z => Z.size_nat z <= bits) row -> Z.size_nat (karr_nth index row) <= bits.
  Proof.
    intro index. induction index as [|index IH]; intros [|z row] bits Hrow.
    - change (0 <= bits). lia.
    - cbn [karr_nth]. inversion Hrow; assumption.
    - change (0 <= bits). lia.
    - cbn [karr_nth]. inversion Hrow as [|q qs Hhead Htail]; subst q qs.
      now apply IH.
  Qed.

  (** Deleting a column preserves every remaining entry's bit bound. *)
  Lemma karr_delete_bits : forall index row bits,
    Forall (fun z => Z.size_nat z <= bits) row ->
    Forall (fun z => Z.size_nat z <= bits) (karr_delete index row).
  Proof.
    intro index. induction index as [|index IH]; intros [|z row] bits Hrow.
    - constructor.
    - cbn [karr_delete]. inversion Hrow; assumption.
    - constructor.
    - cbn [karr_delete]. inversion Hrow as [|q qs Hhead Htail]; subst q qs.
      constructor; [exact Hhead|now apply IH].
  Qed.

  (** Laplace expansion has at most dim products at every recursive determinant level. *)
  Lemma karr_determinant_magnitude : forall order dim bits rows,
    order <= dim -> Forall (Forall (fun z => Z.size_nat z <= bits)) rows ->
    karr_magnitude (karr_determinant order rows) <= (dim * 2^bits)^order.
  Proof.
    intro order. induction order as [|order IH]; intros dim bits rows Horder Hrows.
    - change (1 <= 1). lia.
    - destruct rows as [|row rows].
      + change (0 <= (dim * 2^bits)^S order). lia.
      + inversion Hrows as [|r rs Hrow Htail]; subst r rs.
        set (charge := 2^bits * (dim * 2^bits)^order).
        assert (Hterms : Forall (fun z => karr_magnitude z <= charge)
          (map (fun index =>
            ((if Nat.even index then 1 else -1) * karr_nth index row *
              karr_determinant order (map (karr_delete index) rows))%Z)
            (seq 0 (S order)))).
        { apply Forall_map, Forall_forall. intros index Hindex.
          replace ((if Nat.even index then 1 else -1) * karr_nth index row *
            karr_determinant order (map (karr_delete index) rows))%Z with
            ((if negb (Nat.even index) then -1 else 1) *
              (karr_nth index row *
                karr_determinant order (map (karr_delete index) rows)))%Z
            by (destruct (Nat.even index); cbn [negb]; ring).
          rewrite karr_magnitude_sign, karr_magnitude_mul.
          unfold charge. apply Nat.mul_le_mono.
          - pose proof (karr_magnitude_upper (karr_nth index row)) as Hmagnitude.
            pose proof (karr_nth_bits index row bits Hrow) as Hbits.
            assert (Hpower : 2 ^ Z.size_nat (karr_nth index row) <= 2^bits)
              by (apply Nat.pow_le_mono_r; lia).
            lia.
          - apply IH; [lia|]. apply Forall_map.
            eapply Forall_impl; [|exact Htail]. intros r Hr. now apply karr_delete_bits. }
        pose proof (karr_magnitude_sum _ charge Hterms) as Hsum.
        rewrite length_map, length_seq in Hsum.
        cbn [karr_determinant]. eapply Nat.le_trans; [exact Hsum|].
        unfold charge. rewrite Nat.pow_succ_r by lia.
        replace (S order * (2^bits * (dim * 2^bits)^order)) with
          ((S order * 2^bits) * (dim * 2^bits)^order) by ring.
        apply Nat.mul_le_mono_r, Nat.mul_le_mono_r. exact Horder.
  Qed.

  (** A positive enclosing dimension gives the frozen linear-logarithmic determinant width. *)
  Lemma karr_determinant_bits : forall order dim bits rows,
    1 <= dim -> order <= dim ->
    Forall (Forall (fun z => Z.size_nat z <= bits)) rows ->
    Z.size_nat (karr_determinant order rows) <= ellB dim bits.
  Proof.
    intros order dim bits rows Hdim Horder Hrows.
    destruct order as [|order].
    - change (1 <= ellB dim bits). unfold ellB. nia.
    - pose proof (karr_determinant_magnitude (S order) dim bits rows Horder Hrows)
        as Hmagnitude.
      set (width := bits + Nat.log2 dim + 1).
      assert (Hbase : dim * 2^bits < 2^width).
      { pose proof (karr_log_upper dim) as Hlog.
        assert (Hpositive : 0 < 2^bits).
        { pose proof (Nat.pow_nonzero 2 bits ltac:(lia)). lia. }
        unfold width. replace (bits + Nat.log2 dim + 1) with
          (Nat.log2 dim + 1 + bits) by lia. rewrite Nat.pow_add_r. nia. }
      assert (Hpower : (dim * 2^bits)^S order < (2^width)^S order).
      { apply Nat.pow_lt_mono_l; lia. }
      rewrite <- Nat.pow_mul_r in Hpower.
      apply karr_size_least. eapply Nat.le_lt_trans; [exact Hmagnitude|].
      eapply Nat.lt_le_trans; [exact Hpower|]. apply Nat.pow_le_mono_r; [lia|].
      unfold ellB, width. nia.
  Qed.

  (** Every element in an enumerated subsequence occurs in its original list. *)
  Lemma karr_choose_incl : forall A (xs : list A) order selected,
    In selected (karr_choose order xs) -> incl selected xs.
  Proof.
    intros A xs. induction xs as [|x xs IH]; intros [|order] selected Hin.
    - cbn [karr_choose In] in Hin. destruct Hin as [Hsame|Hin]; [subst selected|contradiction].
      intros y Hy. contradiction.
    - contradiction.
    - rewrite karr_choose_zero in Hin. destruct Hin as [Hsame|Hin]; [subst selected|contradiction].
      intros y Hy. contradiction.
    - cbn [karr_choose] in Hin. apply in_app_or in Hin as [Hin|Hin].
      + apply in_map_iff in Hin as [tail [Hsame Htail]]. subst selected.
        specialize (IH order tail Htail). intros y [Hsame|Hy].
        * now left.
        * right. now apply IH.
      + specialize (IH (S order) selected Hin). intros y Hy. right. now apply IH.
  Qed.

  (** Selecting arbitrary columns preserves the common source-entry width. *)
  Lemma karr_submatrix_bits : forall columns rows bits,
    Forall (Forall (fun z => Z.size_nat z <= bits)) rows ->
    Forall (Forall (fun z => Z.size_nat z <= bits)) (karr_submatrix columns rows).
  Proof.
    intros columns rows bits Hrows. unfold karr_submatrix. apply Forall_map.
    eapply Forall_impl; [|exact Hrows]. intros row Hrow.
    apply Forall_map, Forall_forall. intros index _. now apply karr_nth_bits.
  Qed.

  (** Every independently enumerated signed minor satisfies the same determinant width bound. *)
  Lemma karr_signed_minors_bits : forall width rows dim bits z,
    1 <= dim -> length rows <= dim ->
    Forall (Forall (fun entry => Z.size_nat entry <= bits)) rows ->
    In z (karr_signed_minors width rows) -> Z.size_nat z <= ellB dim bits.
  Proof.
    intros width rows dim bits z Hdim Hlength Hrows Hin.
    unfold karr_signed_minors in Hin. apply in_flat_map in Hin as [order [Horder Hin]].
    apply in_seq in Horder.
    pose proof (Nat.le_min_l (length rows) width) as Hminimum.
    assert (Horder_dim : order <= dim) by lia.
    apply in_flat_map in Hin as [selected [Hselected Hin]].
    apply in_flat_map in Hin as [columns [Hcolumns Hin]].
    assert (Hselected_bits : Forall (Forall (fun entry => Z.size_nat entry <= bits)) selected).
    { apply Forall_forall. intros row Hr.
      apply (proj1 (Forall_forall _ _) Hrows row).
      exact (karr_choose_incl _ rows order selected Hselected row Hr). }
    pose proof (karr_determinant_bits order dim bits (karr_submatrix columns selected)
      Hdim Horder_dim (karr_submatrix_bits columns selected bits Hselected_bits)) as Hbits.
    destruct order as [|[|order]]; cbn [List.In] in Hin;
      destruct Hin as [Heq|Hin]; try (subst z; exact Hbits); try contradiction.
    destruct Hin as [Heq|Hin]; [subst z|contradiction].
    rewrite karr_size_opp. exact Hbits.
  Qed.

  (** A row envelope bounds every entry of the augmented matrix representation. *)
  Lemma karr_row_entries_bits : forall dim mlen bits r,
    karr_row_envelope dim mlen bits r ->
    Forall (fun z => Z.size_nat z <= bits) (karr_row_entries r).
  Proof.
    intros dim mlen bits r [_ [Hcoeff [Hrhs [_ [Hweight Hscale]]]]].
    unfold karr_row_entries. apply Forall_app. split; [exact Hcoeff|].
    constructor; [exact Hrhs|]. apply Forall_app. split; [exact Hweight|].
    constructor; [exact Hscale|constructor].
  Qed.

  (** Prepared source rows fit the raw state's logarithmic arithmetic width. *)
  Lemma karr_bareiss_seeds_bits : forall P,
    Forall (Forall (fun z => Z.size_nat z <= nell (Reached P)))
      (map karr_row_entries (bareiss_seeds P)).
  Proof.
    intro P. unfold bareiss_seeds. apply Forall_map.
    assert (Hprepared : Forall (fun r =>
      NoDup (map fst (lhs r)) /\ C.row_bits r <= nell (Reached P))
      (map normalize_row P)).
    { pose proof (karr_normal_source_width P) as Hwidth.
      apply Forall_forall. intros r Hr. split.
      - apply in_map_iff in Hr as [source [Heq _]]. subst r.
        cbn [normalize_row lhs]. apply normalize_coef_nodup.
      - pose proof (proj1 (Forall_forall _ _) Hwidth r Hr) as Hrow.
        change (C.row_key_bits r + C.row_bits r <= nell (Reached P)) in Hrow. lia. }
    assert (Hpositive : 1 <= nell (Reached P)) by (unfold nell; lia).
    pose proof (karr_seed_rows_envelopes (variables P) (length P) 0
      (map normalize_row P) (length (variables P)) (length P) (nell (Reached P))
      (Nat.le_refl _) (Nat.le_refl _) Hpositive Hprepared) as Hseed.
    eapply Forall_impl; [|exact Hseed].
    intros r Hr. exact (karr_row_entries_bits _ _ _ r Hr).
  Qed.

  (** Arbitrary dense coordinates preserve the prepared seed entry width. *)
  Lemma karr_seed_entries_bits : forall xs P,
    Forall (Forall (fun z => Z.size_nat z <= nell (Reached P)))
      (map karr_row_entries (seed_rows xs (length P) 0 (map normalize_row P))).
  Proof.
    intros xs P. apply Forall_map.
    assert (Hprepared : Forall (fun r =>
      NoDup (map fst (lhs r)) /\ C.row_bits r <= nell (Reached P))
      (map normalize_row P)).
    { pose proof (karr_normal_source_width P) as Hwidth.
      apply Forall_forall. intros r Hr. split.
      - apply in_map_iff in Hr as [source [Heq _]]. subst r.
        cbn [normalize_row lhs]. apply normalize_coef_nodup.
      - pose proof (proj1 (Forall_forall _ _) Hwidth r Hr) as Hrow.
        change (C.row_key_bits r + C.row_bits r <= nell (Reached P)) in Hrow.
        lia. }
    assert (Hpositive : 1 <= nell (Reached P)) by (unfold nell; lia).
    pose proof (karr_seed_rows_envelopes xs (length P) 0
      (map normalize_row P) (length xs) (length P) (nell (Reached P))
      (Nat.le_refl _) (Nat.le_refl _) Hpositive Hprepared) as Hseed.
    eapply Forall_impl; [|exact Hseed].
    intros r Hr. exact (karr_row_entries_bits _ _ _ r Hr).
  Qed.

  (** A generic initialized basis clock follows from the all-order minor law. *)
  Lemma T_karr_bareiss_seed_bounded : forall xs P,
    (T_karr_bareiss (length xs) 1
      (seed_rows xs (length P) 0 (map normalize_row P)) <=
      N.of_nat (length xs) *
        karr_bareiss_stage_budget (length xs + length P + 2)
          (ellB (length xs + length P + 2) (nell (Reached P))) + 4)%N.
  Proof.
    intros xs P.
    eapply T_karr_bareiss_run_bounded with
      (width := length xs + length P + 2)
      (original := map karr_row_entries
        (seed_rows xs (length P) 0 (map normalize_row P)))
      (pivot_rows := []) (pivot_columns := [])
      (columns := seq 0 (length xs + length P + 2))
      (labels := map karr_row_entries
        (seed_rows xs (length P) 0 (map normalize_row P))).
    - apply karr_run_state_seed.
    - rewrite length_map.
      pose proof (karr_seed_rows_length xs (length P) 0 (map normalize_row P))
        as Hlength. rewrite length_map in Hlength. lia.
    - rewrite length_seq. lia.
    - intros z Hz. eapply karr_signed_minors_bits;
        [lia| |apply karr_seed_entries_bits|exact Hz].
      rewrite length_map.
      pose proof (karr_seed_rows_length xs (length P) 0 (map normalize_row P))
        as Hlength. rewrite length_map in Hlength. lia.
  Qed.

  (** Every generic basis entry is an independently enumerated seed minor. *)
  Lemma karr_seed_basis_minor : forall xs P z,
    In z (flat_map karr_row_entries
      (karr_bareiss (length xs) 1
        (seed_rows xs (length P) 0 (map normalize_row P)))) ->
    In z (karr_signed_minors (length xs + length P + 2)
      (map karr_row_entries
        (seed_rows xs (length P) 0 (map normalize_row P)))).
  Proof.
    intros xs P z Hin.
    eapply karr_run_state_record.
    - intro Htwo. rewrite length_map in Htwo.
      assert (Hcount : 2 <= length P).
      { pose proof (karr_seed_rows_length xs (length P) 0
          (map normalize_row P)) as Hlength.
        rewrite length_map in Hlength. lia. }
      destruct (seed_rows xs (length P) 0 (map normalize_row P))
        as [|row rest] eqn:Hseed; [cbn [length] in Htwo; lia|].
      apply karr_signed_minors_entry with (row := karr_row_entries row).
      + apply in_map. now left.
      + pose proof (proj1 (Forall_forall _ _)
          (seed_entries_width xs (length P) 0 (map normalize_row P))
          row ltac:(rewrite Hseed; now left)) as Hwidth.
        rewrite Hwidth. reflexivity.
      + eapply karr_seed_zero; [exact Hcount|rewrite Hseed; now left].
    - apply karr_run_state_seed.
    - now apply karr_bareiss_record_final.
  Qed.

  (** Generic basis rows inherit the same Hadamard input-minor width. *)
  Lemma karr_seed_basis_bits : forall xs P,
    Forall (Forall (fun z => Z.size_nat z <=
      ellB (length xs + length P + 2) (nell (Reached P))))
      (map karr_row_entries
        (karr_bareiss (length xs) 1
          (seed_rows xs (length P) 0 (map normalize_row P)))).
  Proof.
    intros xs P. apply Forall_forall. intros row Hrow.
    apply Forall_forall. intros z Hz.
    eapply (karr_signed_minors_bits (length xs + length P + 2)
      (map karr_row_entries
        (seed_rows xs (length P) 0 (map normalize_row P)))
      (length xs + length P + 2) (nell (Reached P)) z);
      [lia| |apply karr_seed_entries_bits|].
    - rewrite length_map.
      pose proof (karr_seed_rows_length xs (length P) 0
        (map normalize_row P)) as Hlength.
      rewrite length_map in Hlength. lia.
    - apply in_map_iff in Hrow as [source [Heq Hsource]]. subst row.
      apply karr_seed_basis_minor. apply in_flat_map.
      exists source. split; [exact Hsource|exact Hz].
  Qed.

  (** The final generic basis has bounded coordinates and multiplier slots. *)
  Lemma karr_seed_basis_envelope : forall xs P,
    Forall (karr_row_envelope (length xs) (length P)
      (ellB (length xs + length P + 2) (nell (Reached P))))
      (karr_bareiss (length xs) 1
        (seed_rows xs (length P) 0 (map normalize_row P))).
  Proof.
    intros xs P.
    pose proof (karr_bareiss_record_width (length xs) 1
      (seed_rows xs (length P) 0 (map normalize_row P))
      (seed_rows_width xs (length P) 0 (map normalize_row P))) as Hcoeff.
    rewrite karr_bareiss_record_value in Hcoeff.
    pose proof (karr_bareiss_weight_width (length xs) 1
      (seed_rows xs (length P) 0 (map normalize_row P)) (length P)
      (seed_rows_width xs (length P) 0 (map normalize_row P))
      (karr_seed_weight_width xs (length P) 0 (map normalize_row P))) as Hweight.
    pose proof (karr_seed_basis_bits xs P) as Hbits.
    apply Forall_forall. intros row Hr.
    pose proof (proj1 (Forall_forall _ _) Hcoeff row Hr) as Hrcoeff.
    pose proof (proj1 (Forall_forall _ _) Hweight row Hr) as Hrweight.
    pose proof (proj1 (Forall_forall _ _) Hbits (karr_row_entries row)
      (in_map karr_row_entries _ _ Hr)) as Hrentries.
    cbn beta in Hrcoeff, Hrweight, Hrentries.
    apply karr_row_envelope_entries; [lia|lia|exact Hrentries].
  Qed.

  (** A complete elimination run fits the public cubic-Hadamard work shape. *)
  Lemma karr_bareiss_budget_public : forall count dim bits,
    count <= dim ->
    (N.of_nat count * karr_bareiss_stage_budget dim (ellB dim bits) <=
      65536 * N.of_nat ((dim + 1)^3 *
        (ellB (dim + 1) bits + 1)^2))%N.
  Proof.
    intros count dim bits Hcount.
    assert (Hdim : count * (dim + 1) * (dim + dim + 1) <=
      2 * (dim + 1)^3).
    { assert (Hmiddle : dim + dim + 1 <= 2 * (dim + 1)) by lia.
      assert (Hc : count <= dim + 1) by lia.
      eapply Nat.le_trans with (m :=
        (dim + 1) * (dim + 1) * (2 * (dim + 1))).
      - apply Nat.mul_le_mono; [apply Nat.mul_le_mono; lia|exact Hmiddle].
      - replace ((dim + 1)^3) with
          ((dim + 1) * (dim + 1) * (dim + 1))
          by (cbn [Nat.pow]; ring). lia. }
    assert (Hbits : (ellB dim bits + 1)^2 <=
      (ellB (dim + 1) bits + 1)^2).
    { apply Nat.pow_le_mono_l.
      unfold ellB. apply Nat.add_le_mono_r.
      apply Nat.mul_le_mono; [lia|].
      pose proof (Nat.log2_le_mono dim (dim + 1) ltac:(lia)). lia. }
    assert (Hnat : count * (dim + 1) * (dim + dim + 1) *
        (ellB dim bits + 1)^2 <=
      2 * ((dim + 1)^3 * (ellB (dim + 1) bits + 1)^2)).
    { replace (2 * ((dim + 1)^3 * (ellB (dim + 1) bits + 1)^2))
        with ((2 * (dim + 1)^3) * (ellB (dim + 1) bits + 1)^2)
        by ring.
      apply Nat.mul_le_mono; [exact Hdim|exact Hbits]. }
    assert (HN : (N.of_nat (count * (dim + 1) * (dim + dim + 1) *
      (ellB dim bits + 1)^2) <= N.of_nat
      (2 * ((dim + 1)^3 * (ellB (dim + 1) bits + 1)^2)))%N) by lia.
    rewrite !Nat2N.inj_mul in HN.
    unfold karr_bareiss_stage_budget.
    replace (N.of_nat count * (32768 * N.of_nat (dim + 1) *
      N.of_nat (dim + dim + 1) * N.of_nat ((ellB dim bits + 1)^2)))%N with
      (32768 * (N.of_nat count * N.of_nat (dim + 1) *
        N.of_nat (dim + dim + 1) * N.of_nat ((ellB dim bits + 1)^2)))%N
      by ring.
    replace (65536 * N.of_nat ((dim + 1)^3 *
      (ellB (dim + 1) bits + 1)^2))%N with
      (32768 * (2 * N.of_nat ((dim + 1)^3 *
        (ellB (dim + 1) bits + 1)^2)))%N by ring.
    rewrite Nat2N.inj_mul.
    change (N.of_nat 2) with 2%N in HN.
    now apply N.mul_le_mono_l.
  Qed.

  (** The basis clock includes preparation, initialization and elimination. *)
  Lemma T_karr_equality_basis_components : forall xs P,
    (T_equality_basis xs P <=
      T_karr_bareiss (length xs) 1
        (seed_rows xs (length P) 0 (map normalize_row P)) +
      T_seed_rows xs (length P) 0 (map normalize_row P) +
      ListDef.T_map normalize_row T_normalize_row P +
      64 * N.of_nat (length xs + length P + 1))%N.
  Proof.
    intros xs P.
    pose proof (Datatypes.T_length_le xs) as Hxs.
    pose proof (Datatypes.T_length_le P) as Hrows.
    time_unfold T_equality_basis.
    change (fun H : lcons X.t => T_normalize_row H) with T_normalize_row.
    set (preparation := ListDef.T_map normalize_row T_normalize_row P) in *.
    set (initialization := T_seed_rows xs (length P) 0 (map normalize_row P)) in *.
    set (elimination := T_karr_bareiss (length xs) 1
      (seed_rows xs (length P) 0 (map normalize_row P))) in *.
    clearbody preparation initialization elimination.
    rewrite !Nat2N.inj_add in *. cbn [N.of_nat] in *. lia.
  Qed.

  (** Contradiction detection builds one basis and scans it for an empty row. *)
  Lemma T_karr_contradiction_components : forall P,
    (T_contradiction P <= T_variables P +
      T_equality_basis (variables P) P +
      T_empty_certificate P (equality_basis (variables P) P) +
      64 * N.of_nat (length P + 1))%N.
  Proof.
    intros P. time_unfold T_contradiction.
    set (coordinates := T_variables P) in *.
    set (basis := T_equality_basis (variables P) P) in *.
    set (scan := T_empty_certificate P (equality_basis (variables P) P)) in *.
    clearbody coordinates basis scan. lia.
  Qed.

  (** An empty-certificate search pays one bounded check per basis row. *)
  Lemma T_karr_empty_certificate_scan : forall P rs charge,
    (forall r, In r rs ->
      (T_karr_zero r + C.T_check_empty P (kweight r) <= charge)%N) ->
    (T_empty_certificate P rs <=
      (charge + 64) * N.of_nat (length rs + 1))%N.
  Proof.
    intros P rs. induction rs as [|r rs IH]; intros charge Hcharge.
    - time_unfold T_empty_certificate. cbn [length]. lia.
    - pose proof (Hcharge r (or_introl eq_refl)) as Hhead.
      specialize (IH charge (fun q Hq => Hcharge q (or_intror Hq))).
      pose proof (T_karr_zero_test (kright r)) as Hright.
      time_unfold T_empty_certificate.
      time_unfold T_kright. time_unfold T_kweight.
      time_unfold Datatypes.T_negb. time_unfold Datatypes.T_andb.
      destruct (karr_zero r && negb (Z.eqb (kright r) 0) &&
        C.check_empty P (kweight r)); time_simpl; cbn [length];
        rewrite !Nat2N.inj_add in *; cbn [N.of_nat] in *; nia.
  Qed.

  (** A uniform checker and zero-test allowance pays the complete basis scan. *)
  Definition karr_empty_scan_charge (dim keys bits mbits : nat) : N :=
    (C.c_lc * N.of_nat
      ((2 * dim + 1) * (dim + 1) *
        (keys + (mbits + 1) * (bits + 1) + 1) + 1) +
      8 * N.of_nat (dim + 1) + 64)%N.

  Lemma T_karr_empty_certificate_bounded : forall P rs dim keys bits mbits,
    length P <= dim -> length rs <= dim ->
    Forall (fun r => length (lhs r) <= dim /\
      C.row_key_bits r <= keys /\ C.row_bits r <= bits) P ->
    Forall (karr_row_envelope dim dim mbits) rs ->
    (T_empty_certificate P rs <=
      karr_empty_scan_charge dim keys bits mbits * N.of_nat (dim + 1))%N.
  Proof.
    intros P rs dim keys bits mbits HP Hrs Hsource Hbasis.
    assert (Hrow_charge : forall row, In row rs ->
      (T_karr_zero row + C.T_check_empty P (kweight row) <=
        karr_empty_scan_charge dim keys bits mbits - 64)%N).
    { intros row Hr.
      pose proof (proj1 (Forall_forall _ _) Hbasis row Hr) as Hrow.
      destruct Hrow as [Hcoeff [_ [_ [Hweight [Hweight_bits _]]]]].
      pose proof (T_karr_zero_bounded row) as Hzero.
      pose proof (C.T_check_empty_le P (kweight row)) as Hcheck.
      pose proof (karr_csize_envelope P (kweight row) dim keys bits mbits
        Hsource Hweight_bits) as Hsize.
      assert (Hsize_bound : C.csize P (kweight row) <=
        (2 * dim + 1) * (dim + 1) *
          (keys + (mbits + 1) * (bits + 1) + 1)).
      { eapply Nat.le_trans; [exact Hsize|].
        apply Nat.mul_le_mono; [apply Nat.mul_le_mono; lia|lia]. }
      assert (Hcheck_bound : (C.T_check_empty P (kweight row) <=
        C.c_lc * N.of_nat
          ((2 * dim + 1) * (dim + 1) *
            (keys + (mbits + 1) * (bits + 1) + 1) + 1))%N).
      { eapply N.le_trans; [exact Hcheck|].
        apply N.mul_le_mono_l. lia. }
      assert (Hzero_bound : (T_karr_zero row <= 8 * N.of_nat (dim + 1))%N).
      { eapply N.le_trans; [exact Hzero|].
        apply N.mul_le_mono_l. lia. }
      unfold karr_empty_scan_charge. lia. }
    pose proof (T_karr_empty_certificate_scan P rs
      (karr_empty_scan_charge dim keys bits mbits - 64)%N Hrow_charge) as Hscan.
    eapply N.le_trans; [exact Hscan|].
    replace (karr_empty_scan_charge dim keys bits mbits - 64 + 64)%N
      with (karr_empty_scan_charge dim keys bits mbits)%N.
    - now apply N.mul_le_mono_l; lia.
    - unfold karr_empty_scan_charge. lia.
  Qed.

  (** Contradiction scanning uses the initialized basis and the normal source budget. *)
  Lemma T_karr_contradiction_scan_bounded : forall P,
    normal P ->
    (T_empty_certificate P (equality_basis (variables P) P) <=
      karr_empty_scan_charge (n (Reached P) + 2)
        (ell (Reached P)) (ell (Reached P))
        (ellB (length (variables P) + length P + 2) (nell (Reached P))) *
        N.of_nat (n (Reached P) + 3))%N.
  Proof.
    intros P Hnormal.
    replace (n (Reached P) + 3) with ((n (Reached P) + 2) + 1) by lia.
    eapply T_karr_empty_certificate_bounded.
    - unfold n. cbn [rows_of]. lia.
    - unfold equality_basis. rewrite karr_bareiss_length.
      pose proof (karr_seed_rows_length (variables P) (length P) 0
        (map normalize_row P)) as Hlength.
      rewrite length_map in Hlength. unfold n. cbn [rows_of]. lia.
    - eapply Forall_impl; [|apply karr_normal_source_envelope; exact Hnormal].
      intros row [Hlength [Hkeys Hbits]]. repeat split; lia.
    - unfold equality_basis.
      eapply Forall_impl; [|apply karr_seed_basis_envelope].
      intros row Hrow. eapply karr_row_envelope_resize;
        [| | |exact Hrow]; unfold n; cbn [rows_of];
        try (pose proof (karr_variables_count P)); lia.
  Qed.

  (** Independent minors of the initialized augmented matrix fit the frozen ellB bound. *)
  Lemma input_minors_bits : forall P z,
    In z (input_minors P) ->
    Z.size_nat z <= ellB (n (Reached P) + 1) (nell (Reached P)).
  Proof.
    intros P z Hin. unfold input_minors in Hin.
    eapply karr_signed_minors_bits; [lia| |apply karr_bareiss_seeds_bits|exact Hin].
    rewrite length_map. unfold bareiss_seeds.
    pose proof (karr_seed_rows_length (variables P) (length P) 0
      (map normalize_row P)) as Hlength.
    rewrite length_map in Hlength. unfold n. cbn [rows_of]. lia.
  Qed.

  (** The input-minor width fits four copies of the public dimension width. *)
  Lemma karr_minor_width_public : forall P,
    normal P -> ellB (n (Reached P) + 1) (nell (Reached P)) + 1 <=
      4 * (ellB (n (Reached P) + 2) (ell (Reached P)) + 1).
  Proof.
    intros P Hnormal.
    pose proof (karr_normal_terms_log P Hnormal) as Hlog.
    pose proof (Nat.log2_le_mono (n (Reached P) + 1)
      (n (Reached P) + 2) ltac:(lia)) as Hdimlog.
    unfold nell, ellB.
    set (d := n (Reached P)) in *.
    set (b := ell (Reached P)) in *.
    set (l := Nat.log2 (d + 1)) in *.
    set (l' := Nat.log2 (d + 2)) in *.
    set (t := Nat.log2 (terms (Reached P))) in *.
    clearbody d b l l' t.
    nia.
  Qed.

  Lemma bareiss_minor : forall P z, In z (bareiss_entries P) -> In z (input_minors P).
  Proof.
    intros P z Hin. unfold bareiss_entries in Hin. unfold input_minors.
    eapply karr_run_state_record.
    - intro Htwo. rewrite length_map in Htwo.
      assert (Hsource_count : 2 <= length P).
      { unfold bareiss_seeds in Htwo.
        pose proof (karr_seed_rows_length (variables P) (length P) 0
          (map normalize_row P)) as Hcount.
        rewrite length_map in Hcount. lia. }
      apply input_minors_zero; [exact Hsource_count|].
      destruct (bareiss_seeds P) as [|row rows] eqn:Hseeds;
        [cbn [length] in Htwo; lia|discriminate].
    - apply bareiss_run_state_initial.
    - exact Hin.
  Qed.
  (** The initialized elimination run inherits the public input-minor width. *)
  Lemma T_karr_bareiss_initial_bounded : forall P,
    (T_karr_bareiss (length (variables P)) 1 (bareiss_seeds P) <=
      N.of_nat (length (variables P)) *
        karr_bareiss_stage_budget (n (Reached P) + 2)
          (ellB (n (Reached P) + 1) (nell (Reached P))) + 4)%N.
  Proof.
    intro P.
    eapply T_karr_bareiss_run_bounded with
      (width := length (variables P) + length P + 2)
      (original := map karr_row_entries (bareiss_seeds P))
      (pivot_rows := []) (pivot_columns := [])
      (columns := seq 0 (length (variables P) + length P + 2))
      (labels := map karr_row_entries (bareiss_seeds P)).
    - apply bareiss_run_state_initial.
    - rewrite length_map. unfold bareiss_seeds.
      pose proof (karr_seed_rows_length (variables P) (length P) 0
        (map normalize_row P)) as Hlength.
      rewrite length_map in Hlength. unfold n. cbn [rows_of]. lia.
    - rewrite length_seq. unfold n. cbn [rows_of].
      pose proof (karr_variables_count P). lia.
    - intros z Hz. exact (input_minors_bits P z Hz).
  Qed.
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
  Proof.
    intros a b. time_unfold T_narrow. unfold k_karr, lat. nia.
  Qed.
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
