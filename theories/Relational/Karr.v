(** * Linear equality states

    Integer elimination tracks the input multipliers used by every produced row.
    For example, eliminating x from x + y = 2 and x = 1 gives y = 1.
    Builds on: KarrSig and the binary trie code. *)
From Stdlib Require Import List ZArith QArith Bool.
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

(** Dense row arithmetic uses the previous pivot as the Bareiss divisor. *)
Fixpoint karr_cross (d a b : Z) (xs ys : list Z) : list Z :=
  match xs, ys with
  | x :: xs, y :: ys => ((a * x - b * y) / d)%Z :: karr_cross d a b xs ys
  | _, _ => []
  end.

TimeFun karr_cross.

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
  KRow (karr_cross d a b (kcoeff r) (kcoeff p))
    ((a * kright r - b * kright p) / d)%Z
    (karr_cross d a b (kweight r) (kweight p))
    ((a * kscale r - b * kscale p) / d)%Z.

TimeFun karr_reduce.

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

  Definition target_certificate (P : list (lcons X.t)) (c : lcons X.t) : cert :=
    let xs := variables (c :: P) in
    let r := karr_target (equality_basis xs P) 1
      (KRow (dense xs c) (rhs c) (repeat 0%Z (length P)) 1) in
    let sign := if (kscale r <? 0)%Z then (-1)%Z else 1%Z in
    Cert (map (fun z => (- sign * z)%Z) (kweight r)) (Z.abs (kscale r)) false.

  Definition entail_cert (P : list (lcons X.t)) (c : lcons X.t) : option cert :=
    let k := match contradiction P with
      | Some ms => Cert ms 1 false
      | None => target_certificate P c
      end in
    if C.check_entails P c k then Some k else None.

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
  Lemma leb_refl  : forall a, leb a a = true.
  Proof. Admitted. (* STUB *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof. Admitted. (* STUB *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof. Admitted. (* STUB *)
  Lemma is_bot_bot : is_bot bot = true.
  Proof. Admitted. (* STUB *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. Admitted. (* STUB *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof. Admitted. (* STUB *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof. Admitted. (* STUB *)
  Lemma top_greatest : forall a, leb a top = true.
  Proof. Admitted. (* STUB *)
  Lemma widen_ub_l : forall p a b, leb a (widen p a b) = true.
  Proof. Admitted. (* STUB *)
  Lemma widen_ub_r : forall p a b, leb b (widen p a b) = true.
  Proof. Admitted. (* STUB *)
  Lemma widen_stable : forall p a b, leb b a = true -> widen p a b = a.
  Proof. Admitted. (* STUB *)
  Lemma wrank_widen : forall p a b, is_bot a = false -> leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Proof. Admitted. (* STUB *)
  Lemma wrank_widen_le : forall p a b, is_bot a = false -> wrank p (widen p a b) <= wrank p a.
  Proof. Admitted. (* STUB *)
  Lemma narrow_between : forall a b, leb b a = true ->
    leb b (narrow a b) = true /\ leb (narrow a b) a = true.
  Proof. Admitted. (* STUB *)
  Lemma ngamma_mono : forall a b v, leb a b = true -> ngamma a v -> ngamma b v.
  Proof. Admitted. (* STUB *)
  Lemma ngamma_bot : forall v, ~ ngamma bot v.
  Proof. Admitted. (* STUB *)
  Lemma ngamma_top : forall v, ngamma top v.
  Proof. Admitted. (* STUB *)
  Lemma assign_sound : forall x e s st c,
    ngamma s (fun y => N.num (st y)) -> eval_term L.eval st e = Some c ->
    ngamma (assign x e s) (fun y => N.num (upd X.eqb st x c y)).
  Proof. Admitted. (* STUB *)
  Lemma havoc_sound : forall x s st c, ngamma s (fun y => N.num (st y)) ->
    ngamma (havoc x s) (fun y => N.num (upd X.eqb st x c y)).
  Proof. Admitted. (* STUB *)
  Lemma assume_sound : forall g es s st cs,
    ngamma s (fun y => N.num (st y)) -> eval_terms L.eval st es = Some cs ->
    L.holds g cs -> ngamma (assume g es s) (fun y => N.num (st y)).
  Proof. Admitted. (* STUB *)
  Lemma range_sound : forall e s st c,
    ngamma s (fun y => N.num (st y)) -> eval_term L.eval st e = Some c ->
    in_bnd (fst (range e s)) (snd (range e s)) (N.num c).
  Proof. Admitted. (* STUB *)
  Lemma ngamma_reached : forall P v, ngamma (Reached P) v <-> Forall (sat v) P.
  Proof. Admitted. (* STUB *)
  Lemma ngamma_unreached : forall v, ~ ngamma Unreached v.
  Proof. Admitted. (* STUB *)
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
  Proof. Admitted. (* STUB *)
  Lemma leb_complete_Q : forall a b, echelon a ->
    (forall v : X.t -> Q, Forall (satQ v) a -> Forall (satQ v) b) ->
    leb (Reached a) (Reached b) = true.
  Proof. Admitted. (* STUB *)
  Lemma bareiss_minor : forall P z, In z (bareiss_entries P) -> In z (input_minors P).
  Proof. Admitted. (* STUB *)
  Lemma widen_join : forall p a b, widen p a b = if leb b a then a else join a b.
  Proof. Admitted. (* STUB *)
  Lemma entail_cert_checks : forall P c k,
    entail_cert P c = Some k -> C.check_entails P c k = true.
  Proof. Admitted. (* STUB *)
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
