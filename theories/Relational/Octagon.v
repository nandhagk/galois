(** * Integer octagons

    Sparse signed difference matrices support entrywise lattice operations.
    For example, joining upper bounds 3 and 5 retains the weaker bound 5.
    Builds on: OctagonSig, keyed map laws and numeric linearization. *)

From Stdlib Require Import List Bool ZArith NArith Lia ArithRing.
From Argent Require Import Time Tactics Std BigO.
From Galois.Base Require Import KeySig MapSig Code Key.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import EnvSig.
From Galois.Relational Require Import LinForm LinearizeSig NumStateSig OctagonSig Zone.
Local Open Scope nat_scope.

Module OctagonCode (X : KEY_OPS) (K : KEY_OPS with Definition t := (X.t * bool)%type
      with Definition encode := pair_code X.encode BoolKeyCode.encode)
    (M : MAP_OPS K) (L : LANG_OPS) (F : LINEARIZE_OPS X L) <: OCTAGON_OPS X K M L F.
  Definition dbm := M.t (M.t Z).
  Definition t := reach dbm.
  Definition wparam := nat.

  Definition row_of (r : option (M.t Z)) : M.t Z :=
    match r with Some row => row | None => M.empty end.

  Definition bound_leb (a b : option Z) : bool :=
    match a, b with
    | _, None => true
    | Some x, Some y => (x <=? y)%Z
    | None, Some _ => false
    end.

  Definition row_leb (a b : option (M.t Z)) : bool :=
    M.forall2b bound_leb (row_of a) (row_of b).

  Definition leb (a b : t) : bool :=
    match a, b with
    | Unreached, _ => true
    | Reached _, Unreached => false
    | Reached ma, Reached mb => M.forall2b row_leb ma mb
    end.

  Definition bot : t := Unreached.

  Definition is_bot (s : t) : bool :=
    match s with Unreached => true | Reached _ => false end.

  Definition bound_join (a b : option Z) : option Z :=
    match a, b with Some x, Some y => Some (Z.max x y) | _, _ => None end.

  Definition row_join (a b : option (M.t Z)) : option (M.t Z) :=
    match a, b with
    | Some x, Some y => Some (M.merge bound_join x y)
    | _, _ => None
    end.

  Definition join (a b : t) : t :=
    match a, b with
    | Unreached, _ => b
    | _, Unreached => a
    | Reached ma, Reached mb => Reached (M.merge row_join ma mb)
    end.

  Definition top : t := Reached M.empty.

  Definition bound_meet (a b : option Z) : option Z :=
    match a, b with
    | Some x, Some y => Some (Z.min x y)
    | None, _ => b
    | _, None => a
    end.

  Definition row_meet (a b : option (M.t Z)) : option (M.t Z) :=
    match a, b with
    | Some x, Some y => Some (M.merge bound_meet x y)
    | None, _ => b
    | _, None => a
    end.

  Definition meet (a b : t) : t :=
    match a, b with
    | Reached ma, Reached mb => Reached (M.merge row_meet ma mb)
    | _, _ => Unreached
    end.

  Definition bound_widen (a b : option Z) : option Z :=
    match a, b with
    | Some x, Some y => if (y <=? x)%Z then Some x else None
    | _, _ => None
    end.

  Definition row_widen (a b : option (M.t Z)) : option (M.t Z) :=
    match a with
    | Some x => Some (M.merge bound_widen x (row_of b))
    | None => None
    end.

  Definition widen (_ : wparam) (a b : t) : t :=
    if leb b a then a else
      match a, b with
      | Unreached, _ => b
      | _, Unreached => a
      | Reached ma, Reached mb => Reached (M.merge row_widen ma mb)
      end.

  Definition narrow (a b : t) : t := meet a b.

  Definition forget_row (x : X.t) (r : option (M.t Z))
      (_ : option (M.t Z)) : option (M.t Z) :=
    match r with
    | Some row => Some (M.remove (x, true) (M.remove (x, false) row))
    | None => None
    end.

  Definition havoc (x : X.t) (s : t) : t :=
    match s with
    | Unreached => Unreached
    | Reached m =>
      Reached (M.merge (forget_row x)
        (M.remove (x, true) (M.remove (x, false) m)) M.empty)
    end.

  Definition entry (m : dbm) (i j : K.t) : option Z :=
    match M.get i m with Some row => M.get j row | None => None end.

  Definition flip (i : K.t) : K.t := (fst i, negb (snd i)).

  Definition put (i j : K.t) (d : Z) (m : dbm) : dbm :=
    M.set i (M.set j d (row_of (M.get i m))) m.

  Definition lower_bound (d : Z) (old : option Z) : Z :=
    match old with Some z => Z.min d z | None => d end.

  Definition add_cons (i j : K.t) (d : Z) (m : dbm) : dbm :=
    put i j (lower_bound d (entry m i j))
      (put (flip j) (flip i) (lower_bound d (entry m (flip j) (flip i))) m).

  Definition via_bound (a : Z) (old next : option Z) : option Z :=
    match next with
    | Some z => Some (lower_bound (a + z)%Z old)
    | None => old
    end.

  Definition relax_row (prefix : option Z) (row exit : M.t Z) : M.t Z :=
    match prefix with Some a => M.merge (via_bound a) row exit | None => row end.

  Definition round_row (k : K.t) (pivot : M.t Z) (r : option (M.t Z))
      (_ : option (M.t Z)) : option (M.t Z) :=
    match r with
    | Some row => Some (relax_row (M.get k row) row pivot)
    | None => None
    end.

  Definition column_present (k : K.t) (row : M.t Z) : bool :=
    match M.get k row with Some _ => true | None => false end.

  Definition pivot_present (k : K.t) (m : dbm) : bool :=
    match M.get k m with
    | Some _ => true
    | None => M.existsb (column_present k) m
    end.

  (** A zero diagonal is materialized only at an already supported code. *)
  Definition fw_round (k : K.t) (m : dbm) : dbm :=
    let seed := if pivot_present k m then put k k (lower_bound 0%Z (entry m k k)) m else m in
    M.merge (round_row k (row_of (M.get k seed))) seed M.empty.

  Definition remember_key (acc : M.t unit * list K.t) (k : K.t)
      : M.t unit * list K.t :=
    match M.get k (fst acc) with
    | Some _ => acc
    | None => (M.set k tt (fst acc), k :: snd acc)
    end.

  Definition pivot_keys (m : dbm) : list K.t :=
    let es := M.elements m in
    snd (fold_left remember_key
      (map fst es ++ flat_map (fun kv => map fst (M.elements (snd kv))) es)
      (M.empty, nil)).

  Definition nonnegative (k : K.t) (m : dbm) : bool :=
    match entry m k k with Some d => (0 <=? d)%Z | None => true end.

  Fixpoint fw_pivots (ks : list K.t) (m : dbm) : dbm :=
    match ks with
    | nil => m
    | k :: ks =>
      let next := fw_round k m in
      if nonnegative k next then fw_pivots ks next else next
    end.

  Definition fw (m : dbm) : dbm := fw_pivots (pivot_keys m) m.

  Definition replace_row (old fresh : option (M.t Z)) : option (M.t Z) :=
    match old with
    | None => None
    | Some row => match fresh with Some next => Some next | None => Some row end
    end.

  Definition even_bound (d : Z) : Z := (2 * Z.div2 d)%Z.

  (** Each candidate is rounded once, after its label has been validated by lookup. *)
  Definition tighten_row (m changed : dbm) (k : K.t) (_ : M.t Z) : dbm :=
    match M.get k changed with
    | Some _ => changed
    | None =>
      match M.get k m with
      | None => changed
      | Some row =>
        match M.get (flip k) row with
        | None => changed
        | Some d => M.set k (M.set (flip k) (even_bound d) row) changed
        end
      end
    end.

  Definition tighten (m : dbm) : dbm :=
    M.merge replace_row m (M.fold (tighten_row m) m M.empty).

  Definition unary_maps (m : dbm) (acc : M.t Z * M.t Z) (k : K.t)
      (_ : M.t Z) : M.t Z * M.t Z :=
    match entry m k (flip k) with
    | Some d => (M.set k d (fst acc), M.set (flip k) d (snd acc))
    | None => acc
    end.

  Definition strengthen_bound (a : Z) (old unary : option Z) : option Z :=
    match unary with
    | Some b => Some (lower_bound (Z.div2 (a + b)) old)
    | None => old
    end.

  Definition strengthen_outer (unaries : M.t Z)
      (old : option (M.t Z)) (unary : option Z) : option (M.t Z) :=
    match old with
    | Some row =>
      Some (match unary with
        | Some a => M.merge (strengthen_bound a) row unaries
        | None => row
        end)
    | None => None
    end.

  (** The outer merge follows raw codes and preserves the original matrix's labels. *)
  Definition strengthen (m : dbm) : dbm :=
    let unaries := M.fold (unary_maps m) m (M.empty, M.empty) in
    M.merge (strengthen_outer (snd unaries)) m (fst unaries).

  Definition tclose (m : dbm) : t :=
    let ks := pivot_keys m in
    let closed := fw_pivots ks m in
    if forallb (fun k => nonnegative k closed) ks then
      let next := strengthen (tighten closed) in
      if forallb (fun k => nonnegative k next) ks then Reached next else Unreached
    else Unreached.

  Definition edge_prefix (d : Z) (a : option Z) : option Z :=
    match a with Some z => Some (z + d)%Z | None => None end.

  Definition twin_prefix (d : Z) (a cross : option Z) : option Z :=
    match a, cross with
    | Some z, Some c => Some (z + d + c + d)%Z
    | _, _ => None
    end.

  (** Every new path uses each inserted signed edge at most once. *)
  Definition increment_row (i j : K.t) (d : Z) (exit1 exit2 : M.t Z)
      (cross1 cross2 : option Z) (r : option (M.t Z))
      (_ : option (M.t Z)) : option (M.t Z) :=
    match r with
    | None => None
    | Some row =>
      let a := M.get i row in
      let b := M.get (flip j) row in
      let r1 := relax_row (edge_prefix d a) row exit1 in
      let r2 := relax_row (edge_prefix d b) r1 exit2 in
      let r3 := relax_row (twin_prefix d a cross1) r2 exit2 in
      Some (relax_row (twin_prefix d b cross2) r3 exit1)
    end.

  Definition matrix_ok (m : dbm) : bool :=
    M.fold (fun ok k _ => andb ok (nonnegative k m)) m true.

  Definition incr_close (i j : K.t) (d : Z) (m : dbm) : t :=
    let seed := add_cons j j 0%Z (add_cons i i 0%Z m) in
    let next := M.merge
      (increment_row i j d (row_of (M.get j seed)) (row_of (M.get (flip i) seed))
        (entry seed j (flip j)) (entry seed (flip i) i)) seed M.empty in
    if matrix_ok next then
      let tightened := strengthen (tighten next) in
      if matrix_ok tightened then Reached tightened else Unreached
    else Unreached.

  (** Unary signed bounds divide by two, rounding toward negative infinity. *)
  Definition variable_bounds (m : dbm) (x : X.t) : bnd * bnd :=
    (match entry m (x, true) (x, false) with
       Some d => Fin (- Z.div2 d)%Z | None => NegInf end,
     match entry m (x, false) (x, true) with
       Some d => Fin (Z.div2 d) | None => PosInf end).

  Definition form_bounds (m : dbm) (f : lin X.t) : bnd * bnd :=
    rel_form_bounds (variable_bounds m) f.

  Definition range (e : term L.op X.t) (s : t) : bnd * bnd :=
    match s with
    | Unreached => (NegInf, PosInf)
    | Reached m =>
      match F.lin_of e with
      | Some (f, r) => rel_wrap_bounds r (form_bounds m f)
      | None => (NegInf, PosInf)
      end
    end.

  Definition signed_unit (x : X.t) (a : Z) : option K.t :=
    if (a =? 1)%Z then Some (x, true) else
    if (a =? -1)%Z then Some (x, false) else None.

  Inductive oct_shape : Type :=
  | OctConstant
  | OctDifference (i j : K.t) (double : bool).

  Definition reverse_shape (shape : oct_shape) : oct_shape :=
    match shape with
    | OctConstant => OctConstant
    | OctDifference i j double => OctDifference j i double
    end.

  (** A unary expression is doubled; two signed units already form a difference. *)
  Definition difference_pair (cs : list (X.t * Z)) : option oct_shape :=
    match cs with
    | nil => Some OctConstant
    | (x, a) :: nil =>
      match signed_unit x a with
      | Some k => Some (OctDifference (flip k) k true)
      | None =>
        if (a =? 2)%Z then Some (OctDifference (x, false) (x, true) false) else
        if (a =? -2)%Z then Some (OctDifference (x, true) (x, false) false) else None
      end
    | (x, a) :: (y, b) :: nil =>
      match signed_unit x a, signed_unit y b with
      | Some i, Some j => Some (OctDifference (flip j) i false)
      | _, _ => None
      end
    | _ => None
    end.

  (** Recognition inspects at most two coefficients and does not scan rejected forms. *)
  Definition difference_forms (l r : lin X.t) : option oct_shape :=
    match coef l, coef r with
    | nil, rs =>
      match difference_pair rs with Some shape => Some (reverse_shape shape) | None => None end
    | ls, nil => difference_pair ls
    | (x, a) :: nil, (y, b) :: nil =>
      match signed_unit x a, signed_unit y b with
      | Some i, Some j => Some (OctDifference j i false)
      | _, _ => None
      end
    | _, _ => None
    end.

  Definition form_exact (m : dbm) (f : lin X.t) (r : wrapr) : bool :=
    match r with NoWrap => true | _ => rel_wrap_exact r (form_bounds m f) end.

  Definition refine (i j : K.t) (d : Z) (s : t) : t :=
    match s with Unreached => Unreached | Reached m => incr_close i j d m end.

  Definition scale_constraint (double : bool) (d : Z) : Z :=
    if double then (2 * d)%Z else d.

  Definition assume_cmp (c : cmp) (shape : oct_shape) (d : Z) (s : t) : t :=
    match shape with
    | OctConstant =>
      if match c with CLe => (0 <=? d)%Z | CLt => (0 <? d)%Z | CEq => (0 =? d)%Z end
      then s else Unreached
    | OctDifference i j double =>
      match c with
      | CLe => refine i j (scale_constraint double d) s
      | CLt => refine i j (scale_constraint double (d - 1)%Z) s
      | CEq => refine j i (- scale_constraint double d)%Z
          (refine i j (scale_constraint double d) s)
      end
    end.

  Definition assume_atom (s : t) (a : atom X.t) : t :=
    match s with
    | Unreached => Unreached
    | Reached m =>
      match difference_forms (al a) (ar a) with
      | None => s
      | Some shape =>
        if andb (form_exact m (al a) (alw a)) (form_exact m (ar a) (arw a)) then
          assume_cmp (acmp a) shape (cst (ar a) - cst (al a))%Z s
        else s
      end
    end.

  Definition assume (g : L.guard) (es : list (term L.op X.t)) (s : t) : t :=
    match s with
    | Unreached => Unreached
    | Reached _ => fold_left assume_atom (F.atoms_of g es) s
    end.

  Definition copy_source (f : lin X.t) : option K.t :=
    match coef f with (x, a) :: nil => signed_unit x a | _ => None end.

  Definition shift_column_row (k : K.t) (d : Z)
      (r : option (M.t Z)) (_ : option (M.t Z)) : option (M.t Z) :=
    match r with
    | Some row =>
      Some (match M.get k row with
        | Some old => M.set k (old + d)%Z row
        | None => row
        end)
    | None => None
    end.

  Definition shift_columns (k : K.t) (d : Z) (m : dbm) : dbm :=
    M.merge (shift_column_row k d) m M.empty.

  Definition shift_bound (d : Z) (old : option Z) (_ : option Z) : option Z :=
    match old with Some z => Some (z - d)%Z | None => None end.

  Definition shift_literal (k : K.t) (d : Z) (m : dbm) : dbm :=
    let next := shift_columns k d m in
    match M.get k next with
    | Some row => M.set k (M.merge (shift_bound d) row M.empty) next
    | None => next
    end.

  (** A self translation moves the positive and negative literals in opposite directions. *)
  Definition shift (x : X.t) (d : Z) (m : dbm) : dbm :=
    shift_literal (x, false) (-d)%Z (shift_literal (x, true) d m).

  (** A copied source is retained unless it is the negative literal of the assigned variable. *)
  Definition copy_allowed (x : X.t) (source : K.t) : bool :=
    if X.eqb (fst source) x then snd source else true.

  Definition assign_copy (x : X.t) (source : K.t) (d : Z) (s : t) : t :=
    match s with
    | Unreached => Unreached
    | Reached m =>
      if K.eqb source (x, true) then Reached (shift x d m) else
      refine (x, true) source (-d)%Z (refine source (x, true) d (havoc x s))
    end.

  Definition add_range (x : X.t) (bounds : bnd * bnd) (s : t) : t :=
    let lower := match fst bounds with
      | Fin lo => refine (x, true) (x, false) (-2 * lo)%Z s
      | _ => s
      end in
    match snd bounds with
    | Fin hi => refine (x, false) (x, true) (2 * hi)%Z lower
    | _ => lower
    end.

  (** An absent copied bound removes the target column. *)
  Definition put_bound (k : K.t) (bound : option Z) (row : M.t Z) : M.t Z :=
    match bound with Some z => M.set k z row | None => M.remove k row end.

  Definition copy_column_row (target source : K.t) (d : Z)
      (old : option (M.t Z)) (_ : option (M.t Z)) : option (M.t Z) :=
    match old with
    | Some row => Some (put_bound target (edge_prefix d (M.get source row)) row)
    | None => None
    end.

  (** Copying a literal updates its column and then its row from the same source. *)
  Definition copy_literal (target source : K.t) (d : Z) (m : dbm) : dbm :=
    let next := M.merge (copy_column_row target source d) m M.empty in
    M.set target (M.merge (shift_bound d) (row_of (M.get source next)) M.empty) next.

  Definition copy_literals (x : X.t) (source : K.t) (d : Z) (m : dbm) : dbm :=
    copy_literal (x, false) (flip source) (-d)%Z
      (copy_literal (x, true) source d m).

  (** Both signed copies overwrite every old occurrence of the assigned variable. *)
  Definition assign_copy_fast (x : X.t) (source : K.t) (d : Z) (s : t) : t :=
    match s with
    | Unreached => Unreached
    | Reached m =>
      if K.eqb source (x, true) then Reached (shift x d m) else
        Reached (copy_literals x source d (add_cons source source 0%Z m))
    end.

  Definition range_average (bound unary : option Z) (_ : option Z) : option Z :=
    match bound, unary with
    | Some a, Some b => Some (Z.div2 (a + b))
    | _, _ => None
    end.

  Definition range_column_row (x : X.t) (lower upper : option Z)
      (old : option (M.t Z)) (unary : option Z) : option (M.t Z) :=
    match old with
    | Some row =>
      Some (put_bound (x, false) (range_average lower unary None)
        (put_bound (x, true) (range_average upper unary None) row))
    | None => None
    end.

  (** A missing side creates only its zero diagonal, without traversing the unary map. *)
  Definition range_literal_row (x : X.t) (sign : bool) (bound : option Z)
      (unaries : M.t Z) : M.t Z :=
    let row := match bound with
      | Some _ => M.merge (range_average bound) unaries M.empty
      | None => M.empty
      end in
    M.set (x, sign) 0%Z (put_bound (x, negb sign) bound row).

  (** Only the two assigned rows and their columns receive strengthened bounds. *)
  Definition range_matrix (x : X.t) (lower upper : option Z) (m : dbm) : dbm :=
    let unaries := M.fold (unary_maps m) m (M.empty, M.empty) in
    let next := M.merge (range_column_row x lower upper) m (fst unaries) in
    M.set (x, true) (range_literal_row x true lower (snd unaries))
      (M.set (x, false) (range_literal_row x false upper (snd unaries)) next).

  Definition add_range_fast (x : X.t) (bounds : bnd * bnd) (s : t) : t :=
    match s with
    | Unreached => Unreached
    | Reached m =>
      match bounds with
      | (Fin lo, Fin hi) =>
        if (lo <=? hi)%Z then
          Reached (range_matrix x (Some (-2 * lo)%Z) (Some (2 * hi)%Z) m)
        else Unreached
      | (Fin lo, PosInf) => Reached (range_matrix x (Some (-2 * lo)%Z) None m)
      | (NegInf, Fin hi) => Reached (range_matrix x None (Some (2 * hi)%Z) m)
      | (NegInf, PosInf) => s
      | _ => Unreached
      end
    end.

  Definition assign (x : X.t) (e : term L.op X.t) (s : t) : t :=
    match s with
    | Unreached => Unreached
    | Reached m =>
      match F.lin_of e with
      | None => havoc x s
      | Some (f, r) =>
        let bounds := form_bounds m f in
        match copy_source f with
        | Some source =>
          if (if copy_allowed x source then rel_wrap_exact r bounds else false) then
            assign_copy_fast x source (cst f) s
          else add_range_fast x (rel_wrap_bounds r bounds) (havoc x s)
        | None => add_range_fast x (rel_wrap_bounds r bounds) (havoc x s)
        end
      end
    end.
End OctagonCode.

Module Octagon (X : KEY) (K : KEY with Definition t := (X.t * bool)%type
      with Definition encode := pair_code X.encode BoolKeyCode.encode)
    (M : MAP K) (L : LANG) (N : NUM_VIEW L) (F : LINEARIZE X L N) <: OCTAGON X K M L N F.
  Include OctagonCode X K M L F.
  (** Widening rank counts finite entries at their stored row and column codes. *)
  Definition wrank (_ : wparam) (s : t) : nat :=
    match s with
    | Unreached => 0
    | Reached m => fold_right Nat.add 0 (map (fun p =>
        match M.find p m with Some row => length (M.codes row) | None => 0 end) (M.codes m))
    end.
  Definition bar (i : K.t) : K.t := (fst i, negb (snd i)).
  Definition vl (v : X.t -> Z) (i : K.t) : Z :=
    if snd i then v (fst i) else (- v (fst i))%Z.
  Definition models (m : dbm) (v : X.t -> Z) : Prop :=
    forall i j d, entry m i j = Some d -> (vl v j - vl v i <= d)%Z.
  Definition ngamma (s : t) (v : X.t -> Z) : Prop :=
    match s with Unreached => False | Reached m => models m v end.

  (** Flipping a literal negates its integer value. *)
  Lemma vl_flip : forall v i, vl v (flip i) = (- vl v i)%Z.
  Proof.
    intros v [x s]. unfold flip, vl. destruct s; cbn; lia.
  Qed.

  Lemma flip_involutive : forall i, flip (flip i) = i.
  Proof.
    intros [x s]. destruct s; reflexivity.
  Qed.

  (** An absent row supplies no finite bound. *)
  Lemma get_row_of : forall r k,
    M.get k (row_of r) = match r with Some row => M.get k row | None => None end.
  Proof.
    intros [row|] k; [reflexivity|apply M.get_empty].
  Qed.

  Lemma get_set_cases : forall A i j (a : A) m,
    M.get i (M.set j a m) = if K.eqb i j then Some a else M.get i m.
  Proof.
    intros A i j a m. destruct (K.eqb_spec i j) as [Heq|Hneq].
    - subst i. apply M.get_set_same.
    - now apply M.get_set_other.
  Qed.

  (** Writing a matrix entry leaves every other coordinate unchanged. *)
  Lemma entry_put : forall i j d m a b,
    entry (put i j d m) a b =
    if K.eqb a i then if K.eqb b j then Some d else entry m a b else entry m a b.
  Proof.
    intros i j d m a b. unfold entry, put.
    destruct (K.eqb_spec a i) as [Ha|Ha].
    - subst a. rewrite M.get_set_same.
      destruct (K.eqb_spec b j) as [Hb|Hb].
      + subst b. apply M.get_set_same.
      + rewrite M.get_set_other by exact Hb. apply get_row_of.
    - rewrite M.get_set_other by exact Ha. reflexivity.
  Qed.

  (** A minimum retains every value below both its finite operands. *)
  Lemma lower_bound_holds : forall value d old,
    (value <= d)%Z -> (forall z, old = Some z -> (value <= z)%Z) ->
    (value <= lower_bound d old)%Z.
  Proof.
    intros value d [z|] Hnew Hold; cbn [lower_bound].
    - apply Z.min_glb; [exact Hnew|apply Hold; reflexivity].
    - exact Hnew.
  Qed.

  (** A satisfied replacement bound preserves the numeric store. *)
  Lemma models_put : forall i j d m v,
    models m v -> (vl v j - vl v i <= d)%Z -> models (put i j d m) v.
  Proof.
    intros i j d m v Hmodel Hnew a b z Hentry. rewrite entry_put in Hentry.
    destruct (K.eqb_spec a i) as [Ha|Ha].
    - subst a. destruct (K.eqb_spec b j) as [Hb|Hb].
      + subst b. inversion Hentry; subst z. exact Hnew.
      + now apply Hmodel.
    - now apply Hmodel.
  Qed.

  (** The two inserted signed twins express the same inequality. *)
  Lemma models_add_cons : forall i j d m v,
    models m v -> (vl v j - vl v i <= d)%Z -> models (add_cons i j d m) v.
  Proof.
    intros i j d m v Hmodel Hnew. unfold add_cons. apply models_put.
    - apply models_put; [exact Hmodel|]. apply lower_bound_holds.
      + rewrite !vl_flip. lia.
      + intros z Hz. now apply Hmodel.
    - apply lower_bound_holds; [exact Hnew|]. intros z Hz. now apply Hmodel.
  Qed.

  (** A fold preserves any invariant maintained by every callback. *)
  Lemma fold_invariant : forall A B (P : B -> Prop) (f : B -> K.t -> A -> B) m seed,
    P seed -> (forall acc k a, P acc -> P (f acc k a)) -> P (M.fold f m seed).
  Proof.
    intros A B P f m seed Hseed Hstep. rewrite M.fold_spec.
    generalize (M.elements m) as es. intros es. revert seed Hseed.
    induction es as [|[k a] es IH]; intros seed Hseed; cbn [fold_left].
    - exact Hseed.
    - apply IH, Hstep, Hseed.
  Qed.

  (** A fold needs its callback invariant only for the labels it actually visits. *)
  Lemma fold_invariant_elements : forall A B (P : B -> Prop)
      (f : B -> K.t -> A -> B) m seed,
    P seed ->
    (forall acc k a, In (k, a) (M.elements m) -> P acc -> P (f acc k a)) ->
    P (M.fold f m seed).
  Proof.
    intros A B P f m seed Hseed Hstep. rewrite M.fold_spec.
    set (es := M.elements m) in *. clearbody es. revert seed Hseed Hstep.
    induction es as [|[k a] es IH]; intros seed Hseed Hstep; cbn [fold_left].
    - exact Hseed.
    - apply IH.
      + apply Hstep; [now left|exact Hseed].
      + intros acc q b Hin Hacc. apply Hstep; [now right|exact Hacc].
  Qed.

  Lemma empty_models : forall v, models M.empty v.
  Proof.
    intros v i j d Hentry. unfold entry in Hentry.
    rewrite M.get_empty in Hentry. discriminate Hentry.
  Qed.

  (** A validated row lookup inherits the matrix's model. *)
  Lemma row_models : forall m v i row, models m v -> M.get i m = Some row ->
    forall j d, M.get j row = Some d -> (vl v j - vl v i <= d)%Z.
  Proof.
    intros m v i row Hmodel Hrow j d Hentry. apply (Hmodel i j d).
    unfold entry. now rewrite Hrow.
  Qed.

  (** Replacing one row by satisfied bounds preserves the numeric store. *)
  Lemma set_row_models : forall m v i row, models m v ->
    (forall j d, M.get j row = Some d -> (vl v j - vl v i <= d)%Z) ->
    models (M.set i row m) v.
  Proof.
    intros m v i row Hmodel Hrow a b d Hentry. unfold entry in Hentry.
    rewrite get_set_cases in Hentry. destruct (K.eqb_spec a i) as [Ha|Ha].
    - subst a. now apply Hrow.
    - now apply Hmodel.
  Qed.

  (** Row replacement chooses a row from one of two matrices satisfied by the store. *)
  Lemma replace_models : forall m fresh v, models m v -> models fresh v ->
    models (M.merge replace_row m fresh) v.
  Proof.
    intros m fresh v Hmodel Hfresh i j d Hentry. unfold entry in Hentry.
    rewrite M.get_merge in Hentry by reflexivity.
    destruct (M.get i m) as [row|] eqn:Hrow; cbn [replace_row] in Hentry.
    - destruct (M.get i fresh) as [next|] eqn:Hnext.
      + eapply row_models; [exact Hfresh|exact Hnext|exact Hentry].
      + eapply row_models; [exact Hmodel|exact Hrow|exact Hentry].
    - discriminate Hentry.
  Qed.

  (** Integer division by two keeps every integral lower bound on the quotient. *)
  Lemma div2_lower : forall d z, (2 * z <= d)%Z -> (z <= Z.div2 d)%Z.
  Proof.
    intros d z Hle. rewrite Z.div2_div.
    pose proof (Z.div_mod d 2 ltac:(lia)).
    pose proof (Z.mod_pos_bound d 2 ltac:(lia)). lia.
  Qed.

  (** A unary signed difference is even, so rounding its bound down remains sound. *)
  Lemma even_bound_holds : forall v k d,
    (vl v (flip k) - vl v k <= d)%Z ->
    (vl v (flip k) - vl v k <= even_bound d)%Z.
  Proof.
    intros v k d Hle. rewrite vl_flip in *. unfold even_bound.
    pose proof (div2_lower d (- vl v k) ltac:(lia)). lia.
  Qed.

  Lemma tighten_row_models : forall m v changed k row,
    models m v -> models changed v -> models (tighten_row m changed k row) v.
  Proof.
    intros m v changed k ignored Hmodel Hchanged. unfold tighten_row.
    destruct (M.get k changed); [exact Hchanged|].
    destruct (M.get k m) as [row|] eqn:Hrow; [|exact Hchanged].
    destruct (M.get (flip k) row) as [d|] eqn:Hunary; [|exact Hchanged].
    apply set_row_models; [exact Hchanged|]. intros j z Hentry.
    rewrite get_set_cases in Hentry. destruct (K.eqb_spec j (flip k)) as [Hj|Hj].
    - subst j. inversion Hentry; subst z. apply even_bound_holds.
      eapply row_models; [exact Hmodel|exact Hrow|exact Hunary].
    - eapply row_models; [exact Hmodel|exact Hrow|exact Hentry].
  Qed.

  (** Tightening changes only validated unary entries and keeps their integer models. *)
  Lemma tighten_models : forall m v, models m v -> models (tighten m) v.
  Proof.
    intros m v Hmodel. unfold tighten. apply replace_models; [exact Hmodel|].
    apply (fold_invariant _ _ (fun changed => models changed v)).
    - apply empty_models.
    - intros changed k row Hchanged. now apply tighten_row_models.
  Qed.

  (** Both unary maps retain the meaning of the signed bounds they collect. *)
  Definition unary_models (v : X.t -> Z) (unaries : M.t Z * M.t Z) : Prop :=
    (forall k d, M.get k (fst unaries) = Some d -> (vl v (flip k) - vl v k <= d)%Z) /\
    (forall k d, M.get k (snd unaries) = Some d -> (vl v k - vl v (flip k) <= d)%Z).

  Lemma unary_maps_models : forall m v unaries k row,
    models m v -> unary_models v unaries -> unary_models v (unary_maps m unaries k row).
  Proof.
    intros m v unaries k row Hmodel [Hleft Hright]. unfold unary_maps.
    destruct (entry m k (flip k)) as [d|] eqn:Hentry; [|now split].
    split; intros j z Hget; cbn [fst snd] in Hget; rewrite get_set_cases in Hget.
    - destruct (K.eqb_spec j k) as [Hj|Hj].
      + subst j. inversion Hget; subst z. now apply Hmodel.
      + now apply Hleft.
    - destruct (K.eqb_spec j (flip k)) as [Hj|Hj].
      + subst j. inversion Hget; subst z. rewrite flip_involutive. now apply Hmodel.
      + now apply Hright.
  Qed.

  Lemma collect_unary_models : forall m v, models m v ->
    unary_models v (M.fold (unary_maps m) m (M.empty, M.empty)).
  Proof.
    intros m v Hmodel. apply (fold_invariant _ _ (unary_models v)).
    - split; intros k d Hget; cbn [fst snd] in Hget;
        rewrite M.get_empty in Hget; discriminate Hget.
    - intros acc k row Hacc. now apply unary_maps_models.
  Qed.

  (** Unary collection constructs both maps from well-formed insertions. *)
  Lemma collect_unary_wf : forall m,
    M.wf (fst (M.fold (unary_maps m) m (M.empty, M.empty))) /\
    M.wf (snd (M.fold (unary_maps m) m (M.empty, M.empty))).
  Proof.
    intros m. apply (fold_invariant _ _ (fun acc => M.wf (fst acc) /\ M.wf (snd acc))).
    - split; apply M.wf_empty.
    - intros acc k row [Hleft Hright]. unfold unary_maps.
      destruct (entry m k (flip k)); [split; cbn [fst snd]; now apply M.wf_set|now split].
  Qed.

  (** Two unary signed inequalities imply their averaged difference bound. *)
  Lemma strengthen_bound_holds : forall v i j a b,
    (vl v (flip i) - vl v i <= a)%Z ->
    (vl v j - vl v (flip j) <= b)%Z ->
    (vl v j - vl v i <= Z.div2 (a + b))%Z.
  Proof.
    intros v i j a b Ha Hb. rewrite !vl_flip in *. apply div2_lower. lia.
  Qed.

  (** Strengthening adds only constraints implied by the validated unary maps. *)
  Lemma strengthen_models : forall m v, models m v -> models (strengthen m) v.
  Proof.
    intros m v Hmodel. unfold strengthen.
    remember (M.fold (unary_maps m) m (M.empty, M.empty)) as unaries eqn:Hunaries.
    pose proof (collect_unary_models m v Hmodel) as Hsound. rewrite <- Hunaries in Hsound.
    destruct Hsound as [Hleft Hright].
    intros i j d Hentry. unfold entry in Hentry.
    rewrite M.get_merge in Hentry by reflexivity.
    destruct (M.get i m) as [row|] eqn:Hrow; cbn [strengthen_outer] in Hentry;
      [|discriminate Hentry].
    destruct (M.get i (fst unaries)) as [a|] eqn:Ha.
    - rewrite M.get_merge in Hentry by reflexivity. unfold strengthen_bound in Hentry.
      destruct (M.get j (snd unaries)) as [b|] eqn:Hb.
      + inversion Hentry; subst d. apply lower_bound_holds.
        * apply strengthen_bound_holds; [now apply Hleft|now apply Hright].
        * intros old Hold. eapply row_models; [exact Hmodel|exact Hrow|exact Hold].
      + eapply row_models; [exact Hmodel|exact Hrow|exact Hentry].
    - eapply row_models; [exact Hmodel|exact Hrow|exact Hentry].
  Qed.

  (** A row bounds all signed differences measured from its source literal. *)
  Definition row_holds (v : X.t -> Z) (i : K.t) (row : M.t Z) : Prop :=
    forall j d, M.get j row = Some d -> (vl v j - vl v i <= d)%Z.

  Lemma row_of_holds : forall m v i, models m v ->
    row_holds v i (row_of (M.get i m)).
  Proof.
    intros m v i Hmodel j d Hentry. rewrite get_row_of in Hentry.
    apply (Hmodel i j d). exact Hentry.
  Qed.

  (** Relaxation retains values below the old bound and the proposed path bound. *)
  Lemma via_bound_holds : forall value a old next,
    (forall d, old = Some d -> (value <= d)%Z) ->
    (forall z, next = Some z -> (value <= a + z)%Z) ->
    forall d, via_bound a old next = Some d -> (value <= d)%Z.
  Proof.
    intros value a old [z|] Hold Hnext d Hentry; cbn [via_bound] in Hentry.
    - inversion Hentry; subst d. apply lower_bound_holds.
      + apply Hnext. reflexivity.
      + exact Hold.
    - now apply Hold.
  Qed.

  (** A satisfied prefix can be composed with every bound in its exit row. *)
  Lemma relax_row_holds : forall v i k prefix row exit,
    row_holds v i row -> row_holds v k exit ->
    (forall a, prefix = Some a -> (vl v k - vl v i <= a)%Z) ->
    row_holds v i (relax_row prefix row exit).
  Proof.
    intros v i k [a|] row exit Hrow Hexit Hprefix j d Hentry.
    - cbn [relax_row] in Hentry. rewrite M.get_merge in Hentry by reflexivity.
      eapply via_bound_holds; [| |exact Hentry].
      + intros old Hold. now apply Hrow.
      + intros z Hz. pose proof (Hprefix a eq_refl).
        pose proof (Hexit j z Hz). lia.
    - now apply Hrow.
  Qed.

  (** One sparse Floyd-Warshall merge adds only two-edge consequences. *)
  Lemma round_merge_models : forall k m v, models m v ->
    models (M.merge (round_row k (row_of (M.get k m))) m M.empty) v.
  Proof.
    intros k m v Hmodel i j d Hentry. unfold entry in Hentry.
    rewrite M.get_merge in Hentry by reflexivity. rewrite M.get_empty in Hentry.
    destruct (M.get i m) as [row|] eqn:Hrow; cbn [round_row] in Hentry.
    - assert (Hcurrent : row_holds v i row).
      { exact (row_models m v i row Hmodel Hrow). }
      exact (relax_row_holds v i k (M.get k row) row (row_of (M.get k m))
        Hcurrent (row_of_holds m v k Hmodel) (fun a Ha => Hcurrent k a Ha) j d Hentry).
    - discriminate Hentry.
  Qed.

  (** Materializing a zero walk and relaxing through it preserves every model. *)
  Lemma fw_round_models : forall k m v, models m v -> models (fw_round k m) v.
  Proof.
    intros k m v Hmodel. unfold fw_round. apply round_merge_models.
    destruct (pivot_present k m); [|exact Hmodel].
    apply models_put; [exact Hmodel|]. apply lower_bound_holds; [lia|].
    intros d Hd. now apply Hmodel.
  Qed.

  (** Every completed prefix of the pivot loop preserves the original model. *)
  Lemma fw_pivots_models : forall ks m v, models m v -> models (fw_pivots ks m) v.
  Proof.
    intro ks. induction ks as [|k ks IH]; intros m v Hmodel; cbn [fw_pivots].
    - exact Hmodel.
    - pose proof (fw_round_models k m v Hmodel) as Hnext.
      destruct (nonnegative k (fw_round k m)); [now apply IH|exact Hnext].
  Qed.

  Lemma fw_models : forall m v, models m v -> models (fw m) v.
  Proof.
    intros m v Hmodel. unfold fw. now apply fw_pivots_models.
  Qed.

  (** A matrix with a concrete model cannot have a negative diagonal. *)
  Lemma nonnegative_models : forall k m v, models m v -> nonnegative k m = true.
  Proof.
    intros k m v Hmodel. unfold nonnegative.
    destruct (entry m k k) as [d|] eqn:Hentry; [|reflexivity].
    apply Z.leb_le. specialize (Hmodel k k d Hentry). lia.
  Qed.

  Lemma nonnegative_list_models : forall ks m v, models m v ->
    forallb (fun k => nonnegative k m) ks = true.
  Proof.
    intros ks m v Hmodel. apply forallb_forall.
    intros k Hin. now apply (nonnegative_models k m v).
  Qed.

  (** Closure, integer tightening and strengthening all retain the same store. *)
  Lemma tclose_models : forall m v, models m v -> ngamma (tclose m) v.
  Proof.
    intros m v Hmodel. unfold tclose.
    pose proof (fw_pivots_models (pivot_keys m) m v Hmodel) as Hclosed.
    pose proof (tighten_models _ v Hclosed) as Htight.
    pose proof (strengthen_models _ v Htight) as Hnext.
    rewrite (nonnegative_list_models (pivot_keys m) _ v Hclosed).
    rewrite (nonnegative_list_models (pivot_keys m) _ v Hnext). exact Hnext.
  Qed.

  Lemma matrix_ok_models : forall m v, models m v -> matrix_ok m = true.
  Proof.
    intros m v Hmodel. unfold matrix_ok.
    apply (fold_invariant _ _ (fun ok => ok = true)); [reflexivity|].
    intros ok k row Hok. rewrite Hok, (nonnegative_models k m v Hmodel). reflexivity.
  Qed.

  (** The four new path shapes use a new signed edge, its twin, or both. *)
  Lemma increment_models : forall i j d m v,
    models m v -> (vl v j - vl v i <= d)%Z ->
    models (M.merge
      (increment_row i j d (row_of (M.get j m)) (row_of (M.get (flip i) m))
        (entry m j (flip j)) (entry m (flip i) i)) m M.empty) v.
  Proof.
    intros i j d m v Hmodel Hnew a b bound Hentry.
    assert (Htwin : (vl v (flip i) - vl v (flip j) <= d)%Z).
    { rewrite !vl_flip. lia. }
    unfold entry in Hentry. rewrite M.get_merge in Hentry by reflexivity.
    rewrite M.get_empty in Hentry.
    destruct (M.get a m) as [row|] eqn:Hrow; [|discriminate Hentry].
    cbn [increment_row] in Hentry.
    assert (Hcurrent : row_holds v a row).
    { exact (row_models m v a row Hmodel Hrow). }
    assert (Hexit1 : row_holds v j (row_of (M.get j m))) by now apply row_of_holds.
    assert (Hexit2 : row_holds v (flip i) (row_of (M.get (flip i) m)))
      by now apply row_of_holds.
    assert (Hfirst : forall z, edge_prefix d (M.get i row) = Some z ->
      (vl v j - vl v a <= z)%Z).
    { intros z Hz. unfold edge_prefix in Hz.
      destruct (M.get i row) as [prefix|] eqn:Hprefix; [|discriminate Hz].
      inversion Hz; subst z. pose proof (Hcurrent i prefix Hprefix). lia. }
    assert (Hsecond : forall z, edge_prefix d (M.get (flip j) row) = Some z ->
      (vl v (flip i) - vl v a <= z)%Z).
    { intros z Hz. unfold edge_prefix in Hz.
      destruct (M.get (flip j) row) as [prefix|] eqn:Hprefix; [|discriminate Hz].
      inversion Hz; subst z. pose proof (Hcurrent (flip j) prefix Hprefix). lia. }
    assert (Hmixed1 : forall z,
      twin_prefix d (M.get i row) (entry m j (flip j)) = Some z ->
      (vl v (flip i) - vl v a <= z)%Z).
    { intros z Hz. unfold twin_prefix in Hz.
      destruct (M.get i row) as [prefix|] eqn:Hprefix; [|discriminate Hz].
      destruct (entry m j (flip j)) as [cross|] eqn:Hcross; [|discriminate Hz].
      inversion Hz; subst z. pose proof (Hcurrent i prefix Hprefix).
      pose proof (Hmodel j (flip j) cross Hcross). lia. }
    assert (Hmixed2 : forall z,
      twin_prefix d (M.get (flip j) row) (entry m (flip i) i) = Some z ->
      (vl v j - vl v a <= z)%Z).
    { intros z Hz. unfold twin_prefix in Hz.
      destruct (M.get (flip j) row) as [prefix|] eqn:Hprefix; [|discriminate Hz].
      destruct (entry m (flip i) i) as [cross|] eqn:Hcross; [|discriminate Hz].
      inversion Hz; subst z. pose proof (Hcurrent (flip j) prefix Hprefix).
      pose proof (Hmodel (flip i) i cross Hcross). lia. }
    pose proof (relax_row_holds _ _ _ _ _ _ Hcurrent Hexit1 Hfirst) as Hrow1.
    pose proof (relax_row_holds _ _ _ _ _ _ Hrow1 Hexit2 Hsecond) as Hrow2.
    pose proof (relax_row_holds _ _ _ _ _ _ Hrow2 Hexit2 Hmixed1) as Hrow3.
    pose proof (relax_row_holds _ _ _ _ _ _ Hrow3 Hexit1 Hmixed2) as Hrow4.
    exact (Hrow4 b bound Hentry).
  Qed.

  (** Incremental closure preserves each store satisfying the inserted inequality. *)
  Lemma incr_close_models : forall i j d m v,
    models m v -> (vl v j - vl v i <= d)%Z -> ngamma (incr_close i j d m) v.
  Proof.
    intros i j d m v Hmodel Hnew.
    assert (Hseed : models (add_cons j j 0%Z (add_cons i i 0%Z m)) v).
    { apply models_add_cons; [|lia]. apply models_add_cons; [exact Hmodel|lia]. }
    pose proof (increment_models i j d _ v Hseed Hnew) as Hnext.
    pose proof (strengthen_models _ v (tighten_models _ v Hnext)) as Htight.
    unfold incr_close.
    rewrite (matrix_ok_models _ v Hnext), (matrix_ok_models _ v Htight). exact Htight.
  Qed.

  (** Removing both signed literals removes exactly one program variable. *)
  Lemma get_remove_variable : forall A x i (m : M.t A),
    M.get i (M.remove (x, true) (M.remove (x, false) m)) =
    if X.eqb (fst i) x then None else M.get i m.
  Proof.
    intros A x [y sign] m. cbn [fst]. destruct (X.eqb_spec y x) as [Heq|Hneq].
    - subst y. destruct sign.
      + apply M.get_remove_same.
      + rewrite M.get_remove_other by discriminate. apply M.get_remove_same.
    - rewrite !M.get_remove_other by congruence. reflexivity.
  Qed.

  (** Forgetting removes all bounds whose source or destination mentions the variable. *)
  Lemma entry_havoc : forall x m i j,
    entry (M.merge (forget_row x)
      (M.remove (x, true) (M.remove (x, false) m)) M.empty) i j =
    if X.eqb (fst i) x then None else
      if X.eqb (fst j) x then None else entry m i j.
  Proof.
    intros x m i j. unfold entry. rewrite M.get_merge by reflexivity.
    rewrite M.get_empty, get_remove_variable.
    destruct (X.eqb (fst i) x); [reflexivity|].
    destruct (M.get i m) as [row|]; cbn [forget_row].
    - apply get_remove_variable.
    - destruct (X.eqb (fst j) x); reflexivity.
  Qed.

  (** Updating a variable leaves the value of every other signed literal unchanged. *)
  Lemma vl_update_other : forall x st c i,
    fst i <> x ->
    vl (fun y => N.num (upd X.eqb st x c y)) i = vl (fun y => N.num (st y)) i.
  Proof.
    intros x st c [y sign] Hneq. cbn [fst] in Hneq.
    unfold vl, upd. cbn [fst snd].
    destruct (X.eqb_spec y x) as [Heq|Heq]; [contradiction|reflexivity].
  Qed.

  (** A column translation changes exactly the bounds targeting its literal. *)
  Lemma entry_shift_columns : forall k d m i j,
    entry (shift_columns k d m) i j =
    if K.eqb j k then option_map (fun z => (z + d)%Z) (entry m i j)
    else entry m i j.
  Proof.
    intros k d m i j. unfold entry, shift_columns.
    rewrite M.get_merge by reflexivity. rewrite M.get_empty.
    destruct (M.get i m) as [row|]; cbn [shift_column_row].
    - destruct (M.get k row) as [old|] eqn:Hcol.
      + destruct (K.eqb_spec j k) as [Hj|Hj].
        * subst j. rewrite M.get_set_same, Hcol. reflexivity.
        * rewrite M.get_set_other by exact Hj. reflexivity.
      + destruct (K.eqb_spec j k) as [Hj|Hj].
        * subst j. now rewrite Hcol.
        * reflexivity.
    - destruct (K.eqb j k); reflexivity.
  Qed.

  Lemma entry_shift_literal : forall k d m i j,
    entry (shift_literal k d m) i j =
    if K.eqb i k then
      option_map (fun z => (z - d)%Z) (entry (shift_columns k d m) i j)
    else entry (shift_columns k d m) i j.
  Proof.
    intros k d m i j. unfold shift_literal.
    destruct (M.get k (shift_columns k d m)) as [row|] eqn:Hrow.
    - destruct (K.eqb_spec i k) as [Hi|Hi].
      + subst i. unfold entry. rewrite M.get_set_same, Hrow.
        rewrite M.get_merge by reflexivity. rewrite M.get_empty.
        destruct (M.get j row); reflexivity.
      + unfold entry. rewrite M.get_set_other by exact Hi. reflexivity.
    - destruct (K.eqb_spec i k) as [Hi|Hi]; [subst i|reflexivity].
      unfold entry. now rewrite Hrow.
  Qed.

  Definition literal_offset (k : K.t) (d : Z) (i : K.t) : Z :=
    if K.eqb i k then d else 0%Z.

  Definition variable_offset (x : X.t) (d : Z) (i : K.t) : Z :=
    if X.eqb (fst i) x then if snd i then d else (-d)%Z else 0%Z.

  Lemma entry_shift_literal_linear : forall k d m i j,
    entry (shift_literal k d m) i j =
    option_map (fun z => (z + literal_offset k d j - literal_offset k d i)%Z)
      (entry m i j).
  Proof.
    intros k d m i j. rewrite entry_shift_literal, !entry_shift_columns.
    unfold literal_offset. destruct (K.eqb i k), (K.eqb j k), (entry m i j);
      cbn [option_map]; try reflexivity; f_equal; ring.
  Qed.

  Lemma signed_offsets : forall x d i,
    (literal_offset (x, true) d i + literal_offset (x, false) (-d)%Z i)%Z =
    variable_offset x d i.
  Proof.
    intros x d [y sign]. unfold literal_offset, variable_offset. cbn [fst snd].
    destruct (X.eqb_spec y x) as [Heq|Hneq];
      destruct (K.eqb_spec (y, sign) (x, true)) as [Hpos|Hpos];
      destruct (K.eqb_spec (y, sign) (x, false)) as [Hneg|Hneg];
      destruct sign; cbn -[Z.add Z.sub Z.mul Z.opp]; try congruence; lia.
  Qed.

  (** Paired translations add the destination offset and subtract the source offset. *)
  Lemma entry_shift : forall x d m i j,
    entry (shift x d m) i j =
    option_map (fun z => (z + variable_offset x d j - variable_offset x d i)%Z)
      (entry m i j).
  Proof.
    intros x d m i j. unfold shift. rewrite !entry_shift_literal_linear.
    destruct (entry m i j) as [z|]; [|reflexivity]. cbn [option_map].
    rewrite <- (signed_offsets x d i), <- (signed_offsets x d j). f_equal. ring.
  Qed.

  Lemma vl_update_shift : forall x d st c i,
    N.num c = (N.num (st x) + d)%Z ->
    vl (fun y => N.num (upd X.eqb st x c y)) i =
      (vl (fun y => N.num (st y)) i + variable_offset x d i)%Z.
  Proof.
    intros x d st c [y sign] Hvalue. unfold vl, upd, variable_offset. cbn [fst snd].
    destruct (X.eqb_spec y x) as [Heq|Hneq]; [subst y|];
      destruct sign; cbn -[Z.add Z.sub Z.mul Z.opp]; lia.
  Qed.

  (** Translating a variable preserves every existing signed constraint under its update. *)
  Lemma shift_models : forall x offset m st c,
    models m (fun y => N.num (st y)) ->
    N.num c = (N.num (st x) + offset)%Z ->
    models (shift x offset m) (fun y => N.num (upd X.eqb st x c y)).
  Proof.
    intros x offset m st c Hmodel Hvalue i j d Hentry. rewrite entry_shift in Hentry.
    destruct (entry m i j) as [z|] eqn:Hz; [|discriminate Hentry].
    inversion Hentry; subst d. pose proof (Hmodel i j z Hz).
    rewrite (vl_update_shift x offset st c i Hvalue), (vl_update_shift x offset st c j Hvalue).
    lia.
  Qed.

  Lemma vl_update_same : forall x st c,
    vl (fun y => N.num (upd X.eqb st x c y)) (x, true) = N.num c.
  Proof.
    intros x st c. unfold vl, upd. cbn [fst snd].
    destruct (X.eqb_spec x x); [reflexivity|congruence].
  Qed.

  (** Raw entry lookup ignores labels and also treats an absent row as empty. *)
  Definition raw_entry (m : dbm) (p q : positive) : option Z :=
    M.find q (row_of (M.find p m)).

  Lemma row_leb_spec : forall a b,
    row_leb a b = true <->
    forall q, bound_leb (M.find q (row_of a)) (M.find q (row_of b)) = true.
  Proof.
    intros a b. unfold row_leb. apply M.forall2b_spec. reflexivity.
  Qed.

  Lemma row_leb_empty : row_leb None None = true.
  Proof.
    apply row_leb_spec. intros q. cbn [row_of]. rewrite M.find_empty. reflexivity.
  Qed.

  (** Entrywise comparison visits actual codes, including codes with inconsistent labels. *)
  Lemma leb_entries : forall ma mb,
    leb (Reached ma) (Reached mb) = true <->
    forall p q, bound_leb (raw_entry ma p q) (raw_entry mb p q) = true.
  Proof.
    intros ma mb. cbn [leb].
    rewrite (M.forall2b_spec _ _ row_leb ma mb row_leb_empty).
    split; intros H p; apply row_leb_spec; apply H.
  Qed.

  Lemma raw_entry_empty : forall p q, raw_entry M.empty p q = None.
  Proof.
    intros p q. unfold raw_entry. rewrite M.find_empty. apply M.find_empty.
  Qed.

  Lemma raw_entry_get : forall m i j,
    raw_entry m (K.encode i) (K.encode j) = entry m i j.
  Proof.
    intros m i j. unfold raw_entry, entry.
    rewrite <- (M.get_find _ i m). destruct (M.get i m) as [row|]; cbn [row_of].
    - symmetry. apply M.get_find.
    - apply M.find_empty.
  Qed.

  Lemma bound_leb_refl : forall a, bound_leb a a = true.
  Proof.
    intros [z|]; cbn [bound_leb]; [apply Z.leb_refl|reflexivity].
  Qed.

  Lemma bound_leb_trans : forall a b c,
    bound_leb a b = true -> bound_leb b c = true -> bound_leb a c = true.
  Proof.
    intros [a|] [b|] [c|]; cbn [bound_leb]; try congruence.
    repeat rewrite Z.leb_le. lia.
  Qed.

  Lemma raw_entry_join : forall ma mb p q,
    raw_entry (M.merge row_join ma mb) p q =
    bound_join (raw_entry ma p q) (raw_entry mb p q).
  Proof.
    intros ma mb p q. unfold raw_entry.
    rewrite M.find_merge by reflexivity.
    destruct (M.find p ma) as [ra|], (M.find p mb) as [rb|]; cbn [row_join row_of].
    - apply M.find_merge. reflexivity.
    - rewrite M.find_empty. destruct (M.find q ra); reflexivity.
    - rewrite M.find_empty. reflexivity.
    - rewrite M.find_empty. reflexivity.
  Qed.

  Lemma raw_entry_meet : forall ma mb p q,
    raw_entry (M.merge row_meet ma mb) p q =
    bound_meet (raw_entry ma p q) (raw_entry mb p q).
  Proof.
    intros ma mb p q. unfold raw_entry.
    rewrite M.find_merge by reflexivity.
    destruct (M.find p ma) as [ra|], (M.find p mb) as [rb|]; cbn [row_meet row_of].
    - apply M.find_merge. reflexivity.
    - rewrite M.find_empty. destruct (M.find q ra); reflexivity.
    - rewrite M.find_empty. reflexivity.
    - rewrite M.find_empty. reflexivity.
  Qed.

  Lemma raw_entry_widen : forall ma mb p q,
    raw_entry (M.merge row_widen ma mb) p q =
    bound_widen (raw_entry ma p q) (raw_entry mb p q).
  Proof.
    intros ma mb p q. unfold raw_entry.
    rewrite M.find_merge by reflexivity.
    destruct (M.find p ma) as [ra|], (M.find p mb) as [rb|]; cbn [row_widen row_of].
    - apply M.find_merge. reflexivity.
    - rewrite M.find_merge by reflexivity. reflexivity.
    - rewrite M.find_empty. reflexivity.
    - rewrite M.find_empty. reflexivity.
  Qed.

  Lemma bound_join_ub_l : forall a b, bound_leb a (bound_join a b) = true.
  Proof.
    intros [a|] [b|]; cbn [bound_leb bound_join]; try reflexivity.
    apply Z.leb_le, Z.le_max_l.
  Qed.

  Lemma bound_join_ub_r : forall a b, bound_leb b (bound_join a b) = true.
  Proof.
    intros [a|] [b|]; cbn [bound_leb bound_join]; try reflexivity.
    apply Z.leb_le, Z.le_max_r.
  Qed.

  Lemma bound_meet_lb_l : forall a b, bound_leb (bound_meet a b) a = true.
  Proof.
    intros [a|] [b|]; cbn [bound_leb bound_meet]; try reflexivity.
    - apply Z.leb_le, Z.le_min_l.
    - apply Z.leb_refl.
  Qed.

  Lemma bound_meet_greatest : forall a b c,
    bound_leb c a = true -> bound_leb c b = true ->
    bound_leb c (bound_meet a b) = true.
  Proof.
    intros [a|] [b|] [c|]; cbn [bound_leb bound_meet]; try congruence.
    repeat rewrite Z.leb_le. intros Ha Hb. apply Z.min_glb; assumption.
  Qed.

  Lemma bound_widen_ub_l : forall a b, bound_leb a (bound_widen a b) = true.
  Proof.
    intros [a|] [b|]; cbn [bound_widen bound_leb]; try reflexivity.
    destruct (b <=? a)%Z; cbn [bound_leb]; [apply Z.leb_refl|reflexivity].
  Qed.

  Lemma bound_widen_ub_r : forall a b, bound_leb b (bound_widen a b) = true.
  Proof.
    intros [a|] [b|]; cbn [bound_widen bound_leb]; try reflexivity.
    destruct (b <=? a)%Z eqn:Hle; cbn [bound_leb]; [exact Hle|reflexivity].
  Qed.

  (** Every sparse matrix compares below itself, even when labels are inconsistent. *)
  Lemma leb_refl  : forall a, leb a a = true.
  Proof.
    intros [|m]; [reflexivity|]. apply leb_entries. intros p q. apply bound_leb_refl.
  Qed.

  (** Entrywise comparison is transitive. *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof.
    intros [|ma] [|mb] [|mc]; cbn [leb]; try congruence.
    change (leb (Reached ma) (Reached mb) = true ->
      leb (Reached mb) (Reached mc) = true -> leb (Reached ma) (Reached mc) = true).
    rewrite !leb_entries. intros Hab Hbc p q. eapply bound_leb_trans; [apply Hab|apply Hbc].
  Qed.

  (** The unreachable state is below every state. *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof.
    intros a. reflexivity.
  Qed.

  (** The bottom predicate recognizes the unreachable constructor. *)
  Lemma is_bot_bot : is_bot bot = true.
  Proof.
    reflexivity.
  Qed.

  (** Every state recognized as bottom is least. *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof.
    intros [|ma] b Hbot; [reflexivity|discriminate Hbot].
  Qed.

  (** Joining weakens every bound supplied by the left state. *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof.
    intros [|ma] [|mb]; try apply leb_refl; try reflexivity.
    apply leb_entries. intros p q. rewrite raw_entry_join. apply bound_join_ub_l.
  Qed.

  (** Joining weakens every bound supplied by the right state. *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof.
    intros [|ma] [|mb]; try apply leb_refl; try reflexivity.
    apply leb_entries. intros p q. rewrite raw_entry_join. apply bound_join_ub_r.
  Qed.

  (** The empty matrix imposes no upper bounds. *)
  Lemma top_greatest : forall a, leb a top = true.
  Proof.
    intros [|m]; [reflexivity|]. apply leb_entries. intros p q.
    rewrite raw_entry_empty. destruct (raw_entry m p q); reflexivity.
  Qed.

  (** Widening keeps or discards each old finite bound. *)
  Lemma widen_ub_l : forall p a b, leb a (widen p a b) = true.
  Proof.
    intros p a b. unfold widen. destruct (leb b a) eqn:Hle; [apply leb_refl|].
    destruct a as [|ma], b as [|mb]; try apply leb_refl; try reflexivity.
    apply leb_entries. intros i j. rewrite raw_entry_widen. apply bound_widen_ub_l.
  Qed.

  (** A retained old bound is also an upper bound for the candidate. *)
  Lemma widen_ub_r : forall p a b, leb b (widen p a b) = true.
  Proof.
    intros p a b. unfold widen. destruct (leb b a) eqn:Hle; [exact Hle|].
    destruct a as [|ma], b as [|mb]; try apply leb_refl; try reflexivity.
    apply leb_entries. intros i j. rewrite raw_entry_widen. apply bound_widen_ub_r.
  Qed.

  (** A stable candidate returns the exact old representation. *)
  Lemma widen_stable : forall p a b, leb b a = true -> widen p a b = a.
  Proof.
    intros p a b Hle. unfold widen. now rewrite Hle.
  Qed.
  (** A row contributes the distinct pairs formed from its actual stored codes. *)
  Definition row_entry_codes (m : dbm) (p : positive) : list (positive * positive) :=
    match M.find p m with
    | Some row => map (pair p) (M.codes row)
    | None => nil
    end.

  (** Finite-entry counting ignores stored labels at both map levels. *)
  Definition entry_codes (m : dbm) : list (positive * positive) :=
    flat_map (row_entry_codes m) (M.codes m).

  (** The first coordinate of every row entry is its outer stored code. *)
  Lemma row_entry_first : forall m p pq, In pq (row_entry_codes m p) -> fst pq = p.
  Proof.
    intros m p pq Hin. unfold row_entry_codes in Hin.
    destruct (M.find p m) as [row|]; [|contradiction].
    apply in_map_iff in Hin. destruct Hin as [q [Heq Hin]]. now subst pq.
  Qed.

  (** Pairing distinct column codes with one row code preserves distinctness. *)
  Lemma paired_codes_nodup : forall (p : positive) (qs : list positive),
    NoDup qs -> NoDup (map (pair p) qs).
  Proof.
    intros p qs Hcodes. induction Hcodes as [|q qs Hfresh Hcodes IH].
    - constructor.
    - cbn. constructor; [|exact IH]. intro Hin. apply in_map_iff in Hin.
      destruct Hin as [r [Heq Hr]]. injection Heq as Heq. subst r. exact (Hfresh Hr).
  Qed.

  (** Distinct outer codes yield disjoint lists of finite-entry coordinates. *)
  Lemma rows_entry_nodup : forall m ps, NoDup ps ->
    NoDup (flat_map (row_entry_codes m) ps).
  Proof.
    intros m ps Hcodes. induction Hcodes as [|p ps Hfresh Hcodes IH].
    - constructor.
    - cbn [flat_map]. apply NoDup_app; [|exact IH|].
      + unfold row_entry_codes. destruct (M.find p m) as [row|].
        * apply paired_codes_nodup, M.codes_nodup.
        * constructor.
      + intros pq Hfirst Htail. apply in_flat_map in Htail.
        destruct Htail as [q [Hq Hentry]].
        pose proof (row_entry_first m p pq Hfirst) as Hp.
        pose proof (row_entry_first m q pq Hentry) as Hsame.
        apply Hfresh. rewrite <- Hp, Hsame. exact Hq.
  Qed.

  (** No finite raw-code coordinate is counted twice. *)
  Lemma entry_codes_nodup : forall m, NoDup (entry_codes m).
  Proof.
    intro m. unfold entry_codes. apply rows_entry_nodup, M.codes_nodup.
  Qed.

  (** A coordinate occurs exactly when its raw entry is finite. *)
  Lemma entry_codes_spec : forall m p q,
    In (p, q) (entry_codes m) <-> raw_entry m p q <> None.
  Proof.
    intros m p q. split.
    - intro Hin. unfold entry_codes in Hin. apply in_flat_map in Hin.
      destruct Hin as [i [Hi Hin]]. unfold row_entry_codes in Hin.
      destruct (M.find i m) as [row|] eqn:Hrow; [|contradiction].
      apply in_map_iff in Hin. destruct Hin as [j [Heq Hj]].
      injection Heq as Hip Hjq. subst i j.
      unfold raw_entry. rewrite Hrow. cbn [row_of]. now apply M.codes_spec.
    - intro Hentry. unfold raw_entry in Hentry.
      destruct (M.find p m) as [row|] eqn:Hrow; cbn [row_of] in Hentry.
      + unfold entry_codes. apply in_flat_map. exists p. split.
        * apply M.codes_spec. rewrite Hrow. discriminate.
        * unfold row_entry_codes. rewrite Hrow. apply in_map_iff. exists q.
          split; [reflexivity|now apply M.codes_spec].
      + rewrite M.find_empty in Hentry. contradiction.
  Qed.

  (** The flattened coordinate count is the released widening rank. *)
  Lemma entry_codes_rank : forall p m, length (entry_codes m) = wrank p (Reached m).
  Proof.
    intros p m. unfold entry_codes, wrank.
    induction (M.codes m) as [|q qs IH].
    - reflexivity.
    - cbn [flat_map map fold_right]. rewrite length_app, IH.
      unfold row_entry_codes. destruct (M.find q m); cbn; rewrite ?length_map; reflexivity.
  Qed.

  (** Every finite entry retained by widening was already finite in the old matrix. *)
  Lemma widen_codes_incl : forall ma mb,
    incl (entry_codes (M.merge row_widen ma mb)) (entry_codes ma).
  Proof.
    intros ma mb [p q] Hin. apply entry_codes_spec in Hin. apply entry_codes_spec.
    rewrite raw_entry_widen in Hin.
    destruct (raw_entry ma p q) as [d|]; [discriminate|].
    cbn [bound_widen] in Hin. contradiction.
  Qed.

  (** A failed finite Boolean scan provides a member on which its predicate fails. *)
  Lemma forallb_failure : forall (A : Type) (test : A -> bool) xs,
    forallb test xs = false -> exists x, In x xs /\ test x = false.
  Proof.
    intros A test xs. induction xs as [|x xs IH]; intro Hfalse.
    - discriminate Hfalse.
    - cbn in Hfalse. destruct (test x) eqn:Hx.
      + destruct (IH Hfalse) as [y [Hy Htest]]. exists y. split; [now right|exact Htest].
      + exists x. split; [now left|exact Hx].
  Qed.

  (** Failure of entrywise inclusion identifies an old finite bound that widening discards. *)
  Lemma leb_failure_entry : forall ma mb,
    leb (Reached mb) (Reached ma) = false ->
    exists p q, raw_entry ma p q <> None /\
      bound_leb (raw_entry mb p q) (raw_entry ma p q) = false.
  Proof.
    intros ma mb Hfalse.
    destruct (forallb (fun pq =>
      bound_leb (raw_entry mb (fst pq) (snd pq)) (raw_entry ma (fst pq) (snd pq)))
      (entry_codes ma)) eqn:Hscan.
    - assert (Htrue : leb (Reached mb) (Reached ma) = true).
      { apply leb_entries. intros p q.
        destruct (raw_entry ma p q) as [d|] eqn:Hentry.
        - rewrite forallb_forall in Hscan.
          assert (Hin : In (p, q) (entry_codes ma)).
          { apply entry_codes_spec. rewrite Hentry. discriminate. }
          specialize (Hscan (p, q) Hin). cbn in Hscan. now rewrite Hentry in Hscan.
        - destruct (raw_entry mb p q); reflexivity. }
      congruence.
    - apply forallb_failure in Hscan. destruct Hscan as [[p q] [Hin Hfailed]].
      exists p, q. split; [now apply entry_codes_spec|exact Hfailed].
  Qed.

  (** An unstable finite old bound is dropped by the widening callback. *)
  Lemma bound_widen_drops : forall a b,
    bound_leb b a = false -> bound_widen a b = None.
  Proof.
    intros [a|] [b|]; cbn [bound_leb bound_widen]; try congruence.
    intro Hle. now rewrite Hle.
  Qed.

  (** Every unstable widening removes at least one distinct stored coordinate. *)
  Lemma wrank_widen : forall p a b, is_bot a = false -> leb b a = false ->
    wrank p (widen p a b) < wrank p a.
  Proof.
    intros p [|ma] [|mb] Hbot Hunstable; try discriminate.
    unfold widen. rewrite Hunstable.
    change (wrank p (Reached (M.merge row_widen ma mb)) < wrank p (Reached ma)).
    destruct (leb_failure_entry ma mb Hunstable) as [i [j [Hfinite Hfailed]]].
    assert (Hmissing : ~ In (i, j) (entry_codes (M.merge row_widen ma mb))).
    { intro Hin. apply entry_codes_spec in Hin. rewrite raw_entry_widen in Hin.
      rewrite (bound_widen_drops _ _ Hfailed) in Hin. contradiction. }
    assert (Hlength : length ((i, j) :: entry_codes (M.merge row_widen ma mb)) <=
      length (entry_codes ma)).
    { apply NoDup_incl_length.
      - constructor; [exact Hmissing|apply entry_codes_nodup].
      - intros pq [Hpq | Hin].
        + subst pq. now apply entry_codes_spec.
        + exact (widen_codes_incl ma mb pq Hin). }
    change (S (length (entry_codes (M.merge row_widen ma mb))) <=
      length (entry_codes ma)) in Hlength.
    rewrite (entry_codes_rank p (M.merge row_widen ma mb)) in Hlength.
    rewrite (entry_codes_rank p ma) in Hlength. exact Hlength.
  Qed.

  (** Stable widening preserves rank and unstable widening strictly lowers it. *)
  Lemma wrank_widen_le : forall p a b, is_bot a = false -> wrank p (widen p a b) <= wrank p a.
  Proof.
    intros p a b Hbot. destruct (leb b a) eqn:Hstable.
    - rewrite (widen_stable p a b Hstable). reflexivity.
    - apply Nat.lt_le_incl. now apply wrank_widen.
  Qed.
  Lemma narrow_between : forall a b, leb b a = true ->
    leb b (narrow a b) = true /\ leb (narrow a b) a = true.
  Proof.
    intros [|ma] [|mb] Hle; try (split; reflexivity); try discriminate Hle.
    pose proof (proj1 (leb_entries mb ma) Hle) as Hentries.
    split; apply leb_entries; intros p q; cbn [narrow meet].
    - rewrite raw_entry_meet. apply bound_meet_greatest; [apply Hentries|apply bound_leb_refl].
    - rewrite raw_entry_meet. apply bound_meet_lb_l.
  Qed.

  (** Every bound accepted by comparison follows from a source bound. *)
  Lemma ngamma_mono : forall a b v, leb a b = true -> ngamma a v -> ngamma b v.
  Proof.
    intros [|ma] [|mb] v Hle Hmodel; try contradiction; try discriminate Hle.
    pose proof (proj1 (leb_entries ma mb) Hle) as Hentries. intros i j d Hentry.
    specialize (Hentries (K.encode i) (K.encode j)).
    rewrite !raw_entry_get, Hentry in Hentries.
    destruct (entry ma i j) as [c|] eqn:Hsource; [|discriminate Hentries].
    cbn [bound_leb] in Hentries. apply Z.leb_le in Hentries.
    specialize (Hmodel i j c Hsource). lia.
  Qed.

  (** The unreachable constructor has no numeric models. *)
  Lemma ngamma_bot : forall v, ~ ngamma bot v.
  Proof.
    intros v Hmodel. exact Hmodel.
  Qed.

  (** Every numeric store satisfies an empty matrix. *)
  Lemma ngamma_top : forall v, ngamma top v.
  Proof.
    intros v i j d Hentry. unfold entry in Hentry.
    rewrite M.get_empty in Hentry. discriminate Hentry.
  Qed.
  Lemma havoc_sound : forall x s st c, ngamma s (fun y => N.num (st y)) ->
    ngamma (havoc x s) (fun y => N.num (upd X.eqb st x c y)).
  Proof.
    intros x [|m] st c Hmodel; [contradiction|].
    intros i j d Hentry. rewrite entry_havoc in Hentry.
    destruct (X.eqb_spec (fst i) x) as [Hi|Hi]; [discriminate Hentry|].
    destruct (X.eqb_spec (fst j) x) as [Hj|Hj]; [discriminate Hentry|].
    rewrite !vl_update_other by assumption. now apply Hmodel.
  Qed.
  (** Unary entries bound twice the variable, so their halves bound the integer value. *)
  Lemma variable_bounds_sound : forall m v x, models m v ->
    in_bnd (fst (variable_bounds m x)) (snd (variable_bounds m x)) (v x).
  Proof.
    intros m v x Hmodel.
    assert (Hlower : forall d, entry m (x, true) (x, false) = Some d ->
      (- Z.div2 d <= v x)%Z).
    { intros d Hd. pose proof (Hmodel (x, true) (x, false) d Hd) as Hbound.
      unfold vl in Hbound. cbn [fst snd] in Hbound.
      pose proof (div2_lower d (- v x)%Z ltac:(lia)). lia. }
    assert (Hupper : forall d, entry m (x, false) (x, true) = Some d ->
      (v x <= Z.div2 d)%Z).
    { intros d Hd. pose proof (Hmodel (x, false) (x, true) d Hd) as Hbound.
      unfold vl in Hbound. cbn [fst snd] in Hbound. apply div2_lower. lia. }
    unfold variable_bounds.
    destruct (entry m (x, true) (x, false)) as [lo|] eqn:Hlo;
      destruct (entry m (x, false) (x, true)) as [hi|] eqn:Hhi;
      cbn [fst snd in_bnd]; split; try exact I; auto.
  Qed.

  Lemma form_bounds_sound : forall m v f, models m v ->
    in_bnd (fst (form_bounds m f)) (snd (form_bounds m f)) (eval_lin v f).
  Proof.
    intros m v f Hmodel. apply rel_form_bounds_sound.
    intro x. now apply variable_bounds_sound.
  Qed.

  (** A recognized signed unit has exactly its selected literal's value. *)
  Lemma signed_unit_sound : forall x a k v, signed_unit x a = Some k ->
    vl v k = (a * v x)%Z.
  Proof.
    intros x a k v Hunit. unfold signed_unit in Hunit.
    destruct (a =? 1)%Z eqn:Hpos.
    - apply Z.eqb_eq in Hpos. subst a. inversion Hunit; subst k.
      unfold vl. cbn -[Z.add Z.sub Z.mul Z.opp]. ring.
    - destruct (a =? -1)%Z eqn:Hneg; [|discriminate Hunit].
      apply Z.eqb_eq in Hneg. subst a. inversion Hunit; subst k.
      unfold vl. cbn -[Z.add Z.sub Z.mul Z.opp]. ring.
  Qed.

  (** A recognized shape denotes either zero or its possibly doubled signed difference. *)
  Definition shape_relation (v : X.t -> Z) (shape : oct_shape) (z : Z) : Prop :=
    match shape with
    | OctConstant => z = 0%Z
    | OctDifference i j double => scale_constraint double z = (vl v j - vl v i)%Z
    end.

  Lemma reverse_shape_relation : forall v shape z,
    shape_relation v shape z -> shape_relation v (reverse_shape shape) (-z)%Z.
  Proof.
    intros v [|i j double] z Hrelation; [cbn [shape_relation reverse_shape] in *; lia|].
    destruct double; cbn [shape_relation reverse_shape scale_constraint] in *; lia.
  Qed.

  (** Recognition preserves the value of every supported coefficient pattern. *)
  Lemma difference_pair_sound : forall cs v shape,
    difference_pair cs = Some shape -> shape_relation v shape (eval_coef v cs).
  Proof.
    intros cs v shape Hpair. destruct cs as [|[x a] cs].
    - inversion Hpair; subst shape. reflexivity.
    - destruct cs as [|[y b] cs].
      + unfold difference_pair in Hpair.
        destruct (signed_unit x a) as [k|] eqn:Hunit.
        * inversion Hpair; subst shape. unfold shape_relation, scale_constraint.
          rewrite vl_flip, (signed_unit_sound x a k v Hunit).
          unfold eval_coef. cbn -[Z.add Z.sub Z.mul Z.opp]. ring.
        * destruct (a =? 2)%Z eqn:Htwo.
          -- apply Z.eqb_eq in Htwo. subst a. inversion Hpair; subst shape.
             unfold shape_relation, scale_constraint, eval_coef, vl.
             cbn -[Z.add Z.sub Z.mul Z.opp]. ring.
          -- destruct (a =? -2)%Z eqn:Hneg; [|discriminate Hpair].
             apply Z.eqb_eq in Hneg. subst a. inversion Hpair; subst shape.
             unfold shape_relation, scale_constraint, eval_coef, vl.
             cbn -[Z.add Z.sub Z.mul Z.opp]. ring.
      + destruct cs as [|p cs]; [|discriminate Hpair].
        unfold difference_pair in Hpair.
        destruct (signed_unit x a) as [i|] eqn:Hi; [|discriminate Hpair].
        destruct (signed_unit y b) as [j|] eqn:Hj; [|discriminate Hpair].
        inversion Hpair; subst shape. unfold shape_relation, scale_constraint.
        rewrite vl_flip, (signed_unit_sound x a i v Hi), (signed_unit_sound y b j v Hj).
        unfold eval_coef. cbn -[Z.add Z.sub Z.mul Z.opp]. ring.
  Qed.

  Lemma difference_forms_sound : forall l r v shape,
    difference_forms l r = Some shape ->
    shape_relation v shape (eval_coef v (coef l) - eval_coef v (coef r))%Z.
  Proof.
    intros [ls lc] [rs rc] v shape Hpair. unfold difference_forms in Hpair.
    cbn [coef] in Hpair |- *. destruct ls as [|[x a] xs].
    - destruct (difference_pair rs) as [recognized|] eqn:Hrecognized;
        [|discriminate Hpair].
      inversion Hpair; subst shape.
      replace (eval_coef v nil - eval_coef v rs)%Z with (- eval_coef v rs)%Z
        by (unfold eval_coef; cbn; lia).
      apply reverse_shape_relation. now apply difference_pair_sound.
    - destruct rs as [|[y b] ys].
      + change (shape_relation v shape (eval_coef v ((x, a) :: xs) - 0)%Z).
        rewrite Z.sub_0_r. now apply difference_pair_sound.
      + destruct xs as [|p xs], ys as [|q ys]; try discriminate Hpair.
        destruct (signed_unit x a) as [i|] eqn:Hi; [|discriminate Hpair].
        destruct (signed_unit y b) as [j|] eqn:Hj; [|discriminate Hpair].
        inversion Hpair; subst shape. unfold shape_relation, scale_constraint.
        rewrite (signed_unit_sound x a i v Hi), (signed_unit_sound y b j v Hj).
        unfold eval_coef. cbn -[Z.add Z.sub Z.mul Z.opp]. ring.
  Qed.

  Lemma form_exact_sound : forall m f r v, models m v -> form_exact m f r = true ->
    wrap_into r (eval_lin v f) = eval_lin v f.
  Proof.
    intros m f [|lo hi] v Hmodel Hexact; [reflexivity|].
    apply (rel_wrap_exact_sound (WrapTo lo hi) (form_bounds m f)).
    - now apply form_bounds_sound.
    - exact Hexact.
  Qed.

  Lemma refine_sound : forall i j d s v, ngamma s v ->
    (vl v j - vl v i <= d)%Z -> ngamma (refine i j d s) v.
  Proof.
    intros i j d [|m] v Hmodel Hbound; [exact Hmodel|]. now apply incr_close_models.
  Qed.

  Lemma assume_cmp_sound : forall c shape d s v z, ngamma s v ->
    shape_relation v shape z ->
    (match c with CLe => (z <= d)%Z | CLt => (z < d)%Z | CEq => z = d end) ->
    ngamma (assume_cmp c shape d s) v.
  Proof.
    intros c [|i j double] d s v z Hmodel Hrelation Hbound.
    - cbn [shape_relation] in Hrelation. subst z.
      destruct c; cbn [assume_cmp] in *.
      + destruct (0 <=? d)%Z eqn:Htest; [exact Hmodel|].
        apply Z.leb_gt in Htest. lia.
      + destruct (0 <? d)%Z eqn:Htest; [exact Hmodel|].
        apply Z.ltb_ge in Htest. lia.
      + destruct (0 =? d)%Z eqn:Htest; [exact Hmodel|].
        apply Z.eqb_neq in Htest. lia.
    - destruct double, c; cbn [shape_relation scale_constraint assume_cmp] in *;
        repeat (apply refine_sound; [|lia]); exact Hmodel.
  Qed.

  (** Every recognized atom contributes constraints implied by its integer comparison. *)
  Lemma assume_atom_sound : forall s a v, ngamma s v -> atom_holds v a ->
    ngamma (assume_atom s a) v.
  Proof.
    intros [|m] a v Hmodel Hatom; [exact Hmodel|].
    unfold assume_atom. destruct (difference_forms (al a) (ar a)) as [shape|] eqn:Hpair;
      [|exact Hmodel].
    destruct (andb (form_exact m (al a) (alw a))
      (form_exact m (ar a) (arw a))) eqn:Hexact; [|exact Hmodel].
    apply andb_true_iff in Hexact. destruct Hexact as [Hl Hr].
    unfold atom_holds in Hatom.
    rewrite (form_exact_sound m (al a) (alw a) v Hmodel Hl),
      (form_exact_sound m (ar a) (arw a) v Hmodel Hr) in Hatom.
    pose proof (difference_forms_sound (al a) (ar a) v shape Hpair) as Hdiff.
    eapply assume_cmp_sound; [exact Hmodel|exact Hdiff|].
    unfold eval_lin in Hatom. destruct (acmp a); lia.
  Qed.

  Lemma assume_atoms_sound : forall atoms s v, ngamma s v ->
    Forall (atom_holds v) atoms -> ngamma (fold_left assume_atom atoms s) v.
  Proof.
    induction atoms as [|a atoms IH]; intros s v Hmodel Hatoms.
    - exact Hmodel.
    - inversion Hatoms as [|a' atoms' Ha Htail]; subst.
      apply IH; [now apply assume_atom_sound|exact Htail].
  Qed.

  Lemma assume_sound : forall g es s st cs,
    ngamma s (fun y => N.num (st y)) -> eval_terms L.eval st es = Some cs ->
    L.holds g cs -> ngamma (assume g es s) (fun y => N.num (st y)).
  Proof.
    intros g es [|m] st cs Hmodel Heval Hholds; [exact Hmodel|].
    apply assume_atoms_sound; [exact Hmodel|]. now apply (F.atoms_sound g es st cs).
  Qed.

  Lemma range_sound : forall e s st c,
    ngamma s (fun y => N.num (st y)) -> eval_term L.eval st e = Some c ->
    in_bnd (fst (range e s)) (snd (range e s)) (N.num c).
  Proof.
    intros e [|m] st c Hmodel Heval; [contradiction|].
    unfold range. destruct (F.lin_of e) as [[f r]|] eqn:Hlinear.
    - rewrite (F.lin_sound st e c f r Heval Hlinear).
      apply rel_wrap_bounds_sound. now apply form_bounds_sound.
    - unfold in_bnd. cbn. tauto.
  Qed.

  (** The recognized copy source accounts for the whole variable part of the form. *)
  Lemma copy_source_sound : forall f source v, copy_source f = Some source ->
    eval_lin v f = (vl v source + cst f)%Z.
  Proof.
    intros [cs c] source v Hsource. unfold copy_source in Hsource. cbn [coef] in Hsource.
    destruct cs as [|[x a] cs]; [discriminate Hsource|].
    destruct cs as [|p cs]; [|discriminate Hsource].
    pose proof (signed_unit_sound x a source v Hsource) as Hunit.
    unfold eval_lin, eval_coef. cbn [coef cst fold_right fst snd]. rewrite Hunit. lia.
  Qed.

  Lemma copy_allowed_spec : forall x source, copy_allowed x source = true ->
    source = (x, true) \/ fst source <> x.
  Proof.
    intros x [y sign] Hallowed. unfold copy_allowed in Hallowed. cbn [fst snd] in *.
    destruct (X.eqb_spec y x) as [Heq|Hneq].
    - subst y. destruct sign; [now left|discriminate Hallowed].
    - now right.
  Qed.

  Lemma assign_copy_sound : forall x source d s st c,
    copy_allowed x source = true ->
    ngamma s (fun y => N.num (st y)) ->
    N.num c = (vl (fun y => N.num (st y)) source + d)%Z ->
    ngamma (assign_copy x source d s) (fun y => N.num (upd X.eqb st x c y)).
  Proof.
    intros x source d [|m] st c Hallowed Hmodel Hvalue; [exact Hmodel|].
    unfold assign_copy. destruct (K.eqb_spec source (x, true)) as [Heq|Hne].
    - subst source. now apply shift_models.
    - assert (Hvar : fst source <> x).
      { destruct (copy_allowed_spec x source Hallowed) as [Heq|Hvar]; [contradiction|exact Hvar]. }
      apply refine_sound.
      + apply refine_sound.
        * now apply havoc_sound.
        * rewrite vl_update_same, (vl_update_other x st c source Hvar). lia.
      + rewrite vl_update_same, (vl_update_other x st c source Hvar). lia.
  Qed.

  Lemma add_range_sound : forall x bounds s v, ngamma s v ->
    in_bnd (fst bounds) (snd bounds) (v x) -> ngamma (add_range x bounds s) v.
  Proof.
    intros x [lo hi] s v Hmodel Hbounds. unfold add_range, in_bnd in *.
    destruct lo, hi; cbn [fst snd] in *; try contradiction;
      repeat (apply refine_sound; [|unfold vl; cbn [fst snd]; lia]); exact Hmodel.
  Qed.

  (** Optional insertion has the same pointwise equation for finite and absent bounds. *)
  Lemma get_put_bound : forall k bound row j,
    M.get j (put_bound k bound row) =
      if K.eqb j k then bound else M.get j row.
  Proof.
    intros k [z|] row j; unfold put_bound;
      destruct (K.eqb_spec j k) as [Heq|Hneq].
    - subst j. apply M.get_set_same.
    - now apply M.get_set_other.
    - subst j. apply M.get_remove_same.
    - now apply M.get_remove_other.
  Qed.

  Lemma entry_copy_columns : forall target source d m i j,
    entry (M.merge (copy_column_row target source d) m M.empty) i j =
      if K.eqb j target then edge_prefix d (entry m i source) else entry m i j.
  Proof.
    intros target source d m i j. unfold entry.
    rewrite M.get_merge by reflexivity. rewrite M.get_empty.
    destruct (M.get i m) as [row|]; cbn [copy_column_row].
    - apply get_put_bound.
    - destruct (K.eqb j target); reflexivity.
  Qed.

  Definition copy_coordinate (target source i : K.t) : K.t :=
    if K.eqb i target then source else i.

  Lemma entry_copy_literal : forall target source d m i j,
    entry (copy_literal target source d m) i j =
      if K.eqb i target then
        if K.eqb j target then entry m source source else
          option_map (fun z => (z - d)%Z) (entry m source j)
      else if K.eqb j target then
        option_map (fun z => (z + d)%Z) (entry m i source)
      else entry m i j.
  Proof.
    intros target source d m i j. unfold copy_literal.
    destruct (K.eqb_spec i target) as [Heq|Hneq].
    - subst i. unfold entry at 1. rewrite M.get_set_same.
      rewrite M.get_merge by reflexivity. rewrite M.get_empty, get_row_of.
      change (shift_bound d
        (entry (M.merge (copy_column_row target source d) m M.empty) source j) None =
          if K.eqb j target then entry m source source else
            option_map (fun z => (z - d)%Z) (entry m source j)).
      rewrite entry_copy_columns. destruct (K.eqb j target).
      + destruct (entry m source source); cbn [shift_bound edge_prefix];
          [f_equal; lia|reflexivity].
      + destruct (entry m source j); reflexivity.
    - unfold entry at 1. rewrite M.get_set_other by exact Hneq.
      fold (entry (M.merge (copy_column_row target source d) m M.empty) i j).
      rewrite entry_copy_columns. destruct (K.eqb j target);
        [destruct (entry m i source)|]; reflexivity.
  Qed.

  (** A literal copy substitutes one coordinate and translates each incident bound. *)
  Lemma entry_copy_literal_linear : forall target source d m i j,
    entry (copy_literal target source d m) i j =
      option_map (fun z =>
        (z + literal_offset target d j - literal_offset target d i)%Z)
      (entry m (copy_coordinate target source i) (copy_coordinate target source j)).
  Proof.
    intros target source d m i j. rewrite entry_copy_literal.
    unfold literal_offset, copy_coordinate.
    destruct (K.eqb i target), (K.eqb j target).
    - destruct (entry m source source); cbn [option_map]; try reflexivity; f_equal; ring.
    - destruct (entry m source j); cbn [option_map]; try reflexivity; f_equal; ring.
    - destruct (entry m i source); cbn [option_map]; try reflexivity; f_equal; ring.
    - destruct (entry m i j); cbn [option_map]; try reflexivity; f_equal; ring.
  Qed.

  Definition copied_literal (x : X.t) (source i : K.t) : K.t :=
    if X.eqb (fst i) x then if snd i then source else flip source else i.

  Lemma copy_coordinate_pair : forall x source i, fst source <> x ->
    copy_coordinate (x, true) source (copy_coordinate (x, false) (flip source) i) =
      copied_literal x source i.
  Proof.
    intros x [y polarity] [z sign] Hsource.
    unfold copy_coordinate, copied_literal, flip. cbn [fst snd] in *.
    destruct (X.eqb_spec z x) as [Hz|Hz];
      destruct (K.eqb_spec (z, sign) (x, false)) as [Hneg|Hneg].
    - inversion Hneg; subst z sign.
      destruct (K.eqb_spec (y, negb polarity) (x, true)); congruence.
    - destruct (K.eqb_spec (z, sign) (x, true)); destruct sign; congruence.
    - inversion Hneg. contradiction.
    - destruct (K.eqb_spec (z, sign) (x, true)); [congruence|reflexivity].
  Qed.

  Lemma copied_literal_offset : forall x source d i, fst source <> x ->
    literal_offset (x, true) d (copy_coordinate (x, false) (flip source) i) =
      literal_offset (x, true) d i.
  Proof.
    intros x source d i Hsource. unfold copy_coordinate, literal_offset.
    destruct (K.eqb_spec i (x, false)) as [Heq|Hneq]; [subst i|reflexivity].
    destruct (K.eqb_spec (x, false) (x, true)); [discriminate|].
    destruct (K.eqb_spec (flip source) (x, true)) as [Hflip|Hflip]; [|reflexivity].
    destruct source as [y sign]. unfold flip in Hflip. cbn [fst snd] in *. congruence.
  Qed.

  (** The signed pair performs one simultaneous variable substitution. *)
  Lemma entry_copy_literals : forall x source d m i j, fst source <> x ->
    entry (copy_literals x source d m) i j =
      option_map (fun z => (z + variable_offset x d j - variable_offset x d i)%Z)
        (entry m (copied_literal x source i) (copied_literal x source j)).
  Proof.
    intros x source d m i j Hsource. unfold copy_literals.
    rewrite !entry_copy_literal_linear, !copy_coordinate_pair by exact Hsource.
    rewrite !copied_literal_offset by exact Hsource.
    destruct (entry m (copied_literal x source i) (copied_literal x source j)) as [z|];
      [|reflexivity]. cbn [option_map].
    rewrite <- (signed_offsets x d i), <- (signed_offsets x d j). f_equal. ring.
  Qed.

  Lemma vl_update_copy : forall x source d st c i,
    N.num c = (vl (fun y => N.num (st y)) source + d)%Z ->
    vl (fun y => N.num (upd X.eqb st x c y)) i =
      (vl (fun y => N.num (st y)) (copied_literal x source i) +
        variable_offset x d i)%Z.
  Proof.
    intros x source d st c [y sign] Hvalue.
    unfold copied_literal, variable_offset, upd. cbn [fst snd].
    destruct (X.eqb_spec y x) as [Heq|Hneq].
    - subst y. destruct sign; cbn [snd]; rewrite ?vl_flip;
        unfold vl at 1; cbn [fst snd];
        destruct (X.eqb_spec x x); try congruence; lia.
    - unfold vl at 1. cbn [fst snd].
      destruct (X.eqb_spec y x); [contradiction|].
      destruct sign; cbn [vl fst snd]; lia.
  Qed.

  Lemma copy_literals_models : forall x source d m st c,
    fst source <> x -> models m (fun y => N.num (st y)) ->
    N.num c = (vl (fun y => N.num (st y)) source + d)%Z ->
    models (copy_literals x source d m) (fun y => N.num (upd X.eqb st x c y)).
  Proof.
    intros x source d m st c Hsource Hmodel Hvalue i j bound Hentry.
    rewrite entry_copy_literals in Hentry by exact Hsource.
    destruct (entry m (copied_literal x source i) (copied_literal x source j))
      as [z|] eqn:Hz; [|discriminate Hentry].
    inversion Hentry; subst bound.
    pose proof (Hmodel _ _ z Hz) as Hbound.
    rewrite (vl_update_copy x source d st c i Hvalue),
      (vl_update_copy x source d st c j Hvalue). lia.
  Qed.

  (** Fast assignment retains the original soundness contract for both signed copies. *)
  Lemma assign_copy_fast_sound : forall x source d s st c,
    copy_allowed x source = true ->
    ngamma s (fun y => N.num (st y)) ->
    N.num c = (vl (fun y => N.num (st y)) source + d)%Z ->
    ngamma (assign_copy_fast x source d s) (fun y => N.num (upd X.eqb st x c y)).
  Proof.
    intros x source d [|m] st c Hallowed Hmodel Hvalue; [exact Hmodel|].
    unfold assign_copy_fast. destruct (K.eqb_spec source (x, true)) as [Heq|Hneq].
    - subst source. now apply shift_models.
    - apply copy_literals_models; [| |exact Hvalue].
      + destruct (copy_allowed_spec x source Hallowed); [contradiction|assumption].
      + apply models_add_cons; [exact Hmodel|lia].
  Qed.

  Lemma range_average_comm : forall a b,
    range_average a b None = range_average b a None.
  Proof.
    intros [a|] [b|]; cbn [range_average]; try reflexivity.
    now rewrite Z.add_comm.
  Qed.

  Lemma get_range_literal_row : forall x sign bound unaries j,
    M.get j (range_literal_row x sign bound unaries) =
      if K.eqb j (x, sign) then Some 0%Z else
      if K.eqb j (x, negb sign) then bound else
        range_average bound (M.get j unaries) None.
  Proof.
    intros x sign bound unaries j. unfold range_literal_row.
    rewrite get_set_cases, get_put_bound.
    destruct (K.eqb j (x, sign)); [reflexivity|].
    destruct (K.eqb j (x, negb sign)); [reflexivity|].
    destruct bound as [a|]; cbn [range_average].
    - rewrite M.get_merge by reflexivity. rewrite M.get_empty. reflexivity.
    - apply M.get_empty.
  Qed.

  (** A finite average is justified by its two signed unary inequalities. *)
  Lemma range_average_holds : forall v i j bound unary z,
    (forall a, bound = Some a -> (vl v (flip i) - vl v i <= a)%Z) ->
    (forall b, unary = Some b -> (vl v j - vl v (flip j) <= b)%Z) ->
    range_average bound unary None = Some z -> (vl v j - vl v i <= z)%Z.
  Proof.
    intros v i j [a|] [b|] z Ha Hb Haverage; try discriminate Haverage.
    inversion Haverage; subst z. apply strengthen_bound_holds;
      [apply Ha|apply Hb]; reflexivity.
  Qed.

  Lemma range_literal_row_holds : forall x sign bound unaries v,
    (forall a, bound = Some a ->
      (vl v (flip (x, sign)) - vl v (x, sign) <= a)%Z) ->
    (forall j b, M.get j unaries = Some b ->
      (vl v j - vl v (flip j) <= b)%Z) ->
    row_holds v (x, sign) (range_literal_row x sign bound unaries).
  Proof.
    intros x sign bound unaries v Hbound Hunaries j z Hentry.
    rewrite get_range_literal_row in Hentry.
    destruct (K.eqb_spec j (x, sign)) as [Heq|Hneq].
    - subst j. inversion Hentry; subst z. lia.
    - destruct (K.eqb_spec j (x, negb sign)) as [Heq|Hother].
      + subst j. exact (Hbound z Hentry).
      + eapply range_average_holds; [exact Hbound| |exact Hentry].
        intros b Hb. now apply (Hunaries j b).
  Qed.

  Lemma range_column_row_holds : forall x lower upper row unary v i,
    row_holds v i row ->
    (forall a, unary = Some a -> (vl v (flip i) - vl v i <= a)%Z) ->
    (forall a, lower = Some a -> (vl v (x, false) - vl v (x, true) <= a)%Z) ->
    (forall a, upper = Some a -> (vl v (x, true) - vl v (x, false) <= a)%Z) ->
    row_holds v i (row_of (range_column_row x lower upper (Some row) unary)).
  Proof.
    intros x lower upper row unary v i Hrow Hunary Hlower Hupper j z Hentry.
    cbn [range_column_row row_of] in Hentry. rewrite !get_put_bound in Hentry.
    destruct (K.eqb_spec j (x, false)) as [Heq|Hneq].
    - subst j. rewrite range_average_comm in Hentry.
      eapply range_average_holds; [exact Hunary|exact Hlower|exact Hentry].
    - destruct (K.eqb_spec j (x, true)) as [Heq|Hother].
      + subst j. rewrite range_average_comm in Hentry.
        eapply range_average_holds; [exact Hunary|exact Hupper|exact Hentry].
      + now apply Hrow.
  Qed.

  (** Sparse interval assignment adds only consequences of the supplied bounds. *)
  Lemma range_matrix_models : forall x lower upper m v,
    models m v ->
    (forall a, lower = Some a -> (vl v (x, false) - vl v (x, true) <= a)%Z) ->
    (forall a, upper = Some a -> (vl v (x, true) - vl v (x, false) <= a)%Z) ->
    models (range_matrix x lower upper m) v.
  Proof.
    intros x lower upper m v Hmodel Hlower Hupper.
    pose proof (collect_unary_models m v Hmodel) as [Hleft Hright].
    unfold range_matrix. set (unaries := M.fold (unary_maps m) m (M.empty, M.empty)).
    fold unaries in Hleft, Hright.
    intros i j d Hentry. unfold entry at 1 in Hentry.
    rewrite !get_set_cases in Hentry.
    destruct (K.eqb_spec i (x, true)) as [Heq|Hneq].
    - subst i. exact (range_literal_row_holds x true lower (snd unaries) v
        Hlower Hright j d Hentry).
    - destruct (K.eqb_spec i (x, false)) as [Heq|Hother].
      + subst i. exact (range_literal_row_holds x false upper (snd unaries) v
          Hupper Hright j d Hentry).
      + rewrite M.get_merge in Hentry by reflexivity.
        destruct (M.get i m) as [row|] eqn:Hrow; cbn [range_column_row] in Hentry;
          [|discriminate Hentry].
        apply (range_column_row_holds x lower upper row (M.get i (fst unaries)) v i
          (row_models m v i row Hmodel Hrow) (Hleft i) Hlower Hupper j d).
        exact Hentry.
  Qed.

  Lemma add_range_fast_sound : forall x bounds s v, ngamma s v ->
    in_bnd (fst bounds) (snd bounds) (v x) -> ngamma (add_range_fast x bounds s) v.
  Proof.
    intros x [lo hi] [|m] v Hmodel Hbounds; [exact Hmodel|].
    unfold add_range_fast, in_bnd in *. cbn [fst snd] in *.
    destruct Hbounds as [Hlo Hhi].
    destruct lo as [|lo|], hi as [|hi|]; cbn in Hlo, Hhi; try contradiction.
    - apply range_matrix_models; [exact Hmodel| |].
      + intros a Ha. discriminate Ha.
      + intros a Ha. injection Ha as Ha. subst a.
        change (v x - - v x <= 2 * hi)%Z. lia.
    - exact Hmodel.
    - destruct (lo <=? hi)%Z eqn:Horder.
      + apply range_matrix_models; [exact Hmodel| |].
        * intros a Ha. injection Ha as Ha. subst a.
          change (- v x - v x <= -2 * lo)%Z. lia.
        * intros a Ha. injection Ha as Ha. subst a.
          change (v x - - v x <= 2 * hi)%Z. lia.
      + apply Z.leb_gt in Horder. lia.
    - apply range_matrix_models; [exact Hmodel| |].
      + intros a Ha. injection Ha as Ha. subst a.
        change (- v x - v x <= -2 * lo)%Z. lia.
      + intros a Ha. discriminate Ha.
  Qed.

  Lemma assign_sound : forall x e s st c,
    ngamma s (fun y => N.num (st y)) -> eval_term L.eval st e = Some c ->
    ngamma (assign x e s) (fun y => N.num (upd X.eqb st x c y)).
  Proof.
    intros x e [|m] st c Hmodel Heval; [exact Hmodel|].
    unfold assign. destruct (F.lin_of e) as [[f r]|] eqn:Hlinear;
      [|now apply havoc_sound].
    pose proof (F.lin_sound st e c f r Heval Hlinear) as Hvalue.
    pose proof (form_bounds_sound m (fun y => N.num (st y)) f Hmodel) as Hbounds.
    assert (Hwrapped : in_bnd
      (fst (rel_wrap_bounds r (form_bounds m f)))
      (snd (rel_wrap_bounds r (form_bounds m f))) (N.num c)).
    { rewrite Hvalue. now apply rel_wrap_bounds_sound. }
    assert (Hupdate : N.num (upd X.eqb st x c x) = N.num c).
    { unfold upd. destruct (X.eqb_spec x x); [reflexivity|congruence]. }
    destruct (copy_source f) as [source|] eqn:Hsource.
    - destruct (copy_allowed x source) eqn:Hallowed; cbn beta iota zeta.
      + destruct (rel_wrap_exact r (form_bounds m f)) eqn:Hwrap.
        * apply assign_copy_fast_sound; [exact Hallowed|exact Hmodel|].
          rewrite Hvalue, (rel_wrap_exact_sound r (form_bounds m f) _ Hbounds Hwrap).
          now apply copy_source_sound.
        * apply add_range_fast_sound; [now apply havoc_sound|]. now rewrite Hupdate.
      + apply add_range_fast_sound; [now apply havoc_sound|]. now rewrite Hupdate.
    - apply add_range_fast_sound; [now apply havoc_sound|]. now rewrite Hupdate.
  Qed.

  Lemma entry_spec : forall m i j,
    entry m i j = match M.get i m with Some row => M.get j row | None => None end.
  Proof.
    reflexivity.
  Qed.

  (** Reached matrices use the signed difference semantics. *)
  Lemma ngamma_reached : forall m v, ngamma (Reached m) v <-> models m v.
  Proof.
    reflexivity.
  Qed.

  (** Unreachable matrices have no numeric models. *)
  Lemma ngamma_unreached : forall v, ~ ngamma Unreached v.
  Proof.
    intros v Hmodel. exact Hmodel.
  Qed.
End Octagon.

Module OctagonT (X : KEY_T) (K : KEY_T with Definition t := (X.t * bool)%type
      with Definition encode := pair_code X.encode BoolKeyCode.encode)
    (M : MAP_T K) (L : LANG_T) (N : NUM_VIEW L) (F : LINEARIZE_T X L N)
    <: OCTAGON_ALL X K M L N F.
  Include Octagon X K M L N F.
  Definition wsize (_ : wparam) : nat := 0.
  Definition rows (m : dbm) : list (M.t Z) :=
    flat_map (fun p => match M.find p m with Some r => r :: nil | None => nil end) (M.codes m).
  Definition support (m : dbm) : list positive :=
    fold_left (fun acc p => if existsb (Pos.eqb p) acc then acc else p :: acc)
      (M.codes m ++ flat_map M.codes (rows m)) nil.
  Definition supp (m : dbm) : nat := length (support m).
  Definition b (m : dbm) : nat := fold_right Nat.max 0 (map Pos.size_nat (support m)).
  Definition ell (m : dbm) : nat := fold_right Nat.max 0 (flat_map (fun r =>
    map (fun q => match M.find q r with Some z => Z.size_nat z | None => 0 end) (M.codes r))
    (rows m)).
  Definition skel (m : dbm) : nat := M.nodes m + fold_right Nat.add 0 (map M.nodes (rows m)).
  Definition skels (s : t) : nat := match s with Unreached => 0 | Reached m => skel m end.
  Definition entries (s : t) : nat :=
    match s with
    | Unreached => 0
    | Reached m => length (M.codes m) +
        fold_right Nat.add 0 (map (fun r => length (M.codes r)) (rows m))
    end.
  Definition labs (s : t) : nat := match s with Unreached => 0 | Reached m => M.weight m end.
  Definition keys (m : dbm) : list K.t :=
    fold_left (fun acc x => if existsb (K.eqb x) acc then acc else x :: acc)
      (map fst (M.elements m) ++
       flat_map (fun kv => map fst (M.elements (snd kv))) (M.elements m)) nil.
  TimeFun keys.
  Definition dbm_wf (m : dbm) : Prop :=
    M.wf m /\ forall p r, M.find p m = Some r -> M.wf r.
  Definition ns (s : t) := match s with Unreached => 0 | Reached m => supp m end.
  Definition bs (s : t) := match s with Unreached => 0 | Reached m => b m end.
  Definition ells (s : t) := match s with Unreached => 0 | Reached m => ell m end.
  Definition size (s : t) : nat :=
    (ns s + 1)^2 * (bs s + ells s + 1) + skels s.
  Definition lin_bits (e : term L.op X.t) : nat :=
    match F.lin_of e with
    | Some (f, r) =>
      fold_right Nat.max (Z.size_nat (cst f))
        (map (fun p => Z.size_nat (snd p)) (coef f)) +
      match r with NoWrap => 0 | WrapTo lo hi => Z.size_nat lo + Z.size_nat hi end
    | None => 0
    end.
  Definition wunits (s : t) : nat := (ns s + 1) ^ 2.
  Definition assign_work (x : X.t) (e : term L.op X.t) (s : t) : nat :=
    (ns s + 1)^2 * (bs s + ells s + X.bits x + F.bits_e e + lin_bits e + 1) +
      skels s + labs s +
      (tsize e + 1) * (bs s + ells s + F.bits_e e + Nat.log2 (tsize e) + 1)^2 +
      N.to_nat (F.T_lin_of e).
  Definition havoc_work (x : X.t) (s : t) : nat :=
    (ns s + 1)^2 * (bs s + X.bits x + ells s + 1) + skels s.
  Definition assume_work (g : L.guard) (es : list (term L.op X.t)) (s : t) : nat :=
    length (F.atoms_of g es) * (ns s + 2 * length (F.atoms_of g es) + 1)^2 *
      (bs s + ells s + F.bits_es g es + 2 * length (F.atoms_of g es) + 1) +
      length (F.atoms_of g es) * labs s +
      N.to_nat (F.T_atoms_of g es).
  Definition range_work (e : term L.op X.t) (s : t) : nat :=
    (tsize e + 1) * (bs s + ells s + F.bits_e e + Nat.log2 (tsize e) + 1)^2 +
      N.to_nat (F.T_lin_of e).
  Definition range_bits (e : term L.op X.t) (s : t) : nat :=
    ells s + F.bits_e e + Nat.log2 (tsize e) + 2.
  TimeFun row_of.
  TimeFun bound_leb.
  TimeFun row_leb.
  TimeFun bound_join.
  TimeFun row_join.
  TimeFun bound_meet.
  TimeFun row_meet.
  TimeFun bound_widen.
  TimeFun row_widen.
  TimeFun forget_row.
  TimeFun flip.
  TimeFun put.
  TimeFun lower_bound.
  TimeFun entry.
  TimeFun add_cons.
  TimeFun via_bound.
  TimeFun relax_row.
  TimeFun round_row.
  TimeFun column_present.
  TimeFun pivot_present.
  TimeFun fw_round.
  TimeFun remember_key.
  TimeFun pivot_keys.
  TimeFun nonnegative.
  TimeFun fw_pivots.
  TimeFun replace_row.
  TimeFun even_bound.
  TimeFun tighten_row.
  TimeFun unary_maps.
  TimeFun strengthen_bound.
  TimeFun strengthen_outer.
  TimeFun edge_prefix.
  TimeFun twin_prefix.
  TimeFun increment_row.
  TimeFun matrix_ok.
  TimeFun fw.
  TimeFun tighten.
  TimeFun strengthen.
  TimeFun tclose.
  TimeFun incr_close.
  TimeFun variable_bounds.
  TimeFun form_bounds.
  TimeFun signed_unit.
  TimeFun reverse_shape.
  TimeFun difference_pair.
  TimeFun difference_forms.
  TimeFun form_exact.
  TimeFun refine.
  TimeFun scale_constraint.
  TimeFun assume_cmp.
  TimeFun assume_atom.
  TimeFun copy_source.
  TimeFun shift_column_row.
  TimeFun shift_columns.
  TimeFun shift_bound.
  TimeFun shift_literal.
  TimeFun shift.
  TimeFun copy_allowed.
  TimeFun havoc.
  TimeFun assign_copy.
  TimeFun add_range.
  TimeFun put_bound.
  TimeFun copy_column_row.
  TimeFun copy_literal.
  TimeFun copy_literals.
  TimeFun assign_copy_fast.
  TimeFun range_average.
  TimeFun range_column_row.
  TimeFun range_literal_row.
  TimeFun range_matrix.
  TimeFun add_range_fast.
  TimeFun bot.
  TimeFun top.
  TimeFun meet.
  TimeFun leb.
  TimeFun join.
  TimeFun is_bot.
  TimeFun widen.
  TimeFun narrow.
  TimeFun assign.
  TimeFun assume.
  TimeFun range.
  Lemma T_row_of_le : forall r, (T_row_of r <= 1)%N.
  Proof.
    intros [row|]; time_step.
  Qed.

  Definition c_lat : N := (256 * (M.c_map + 1) * (M.c_map + 1))%N.
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof.
    unfold c_lat. nia.
  Qed.
  Definition c_num : N :=
    (281474976710656 * (M.c_map + K.c_key + X.c_key + 1) *
      (M.c_map + K.c_key + X.c_key + 1))%N.
  (** Signed literal encodings add the Boolean sign bit to the doubled variable code. *)
  Lemma literal_bits : forall x sign,
    K.bits (x, sign) = 2 * X.bits x + (if sign then 1 else 0).
  Proof.
    intros x sign.
    change (Pos.size_nat (glue (X.encode x) (BoolKeyCode.encode sign)) =
      2 * Pos.size_nat (X.encode x) + (if sign then 1 else 0)).
    rewrite glue_bits. destruct sign; cbn [BoolKeyCode.encode Pos.size_nat]; lia.
  Qed.

  Lemma flip_bits : forall i, K.bits (flip i) <= K.bits i + 1.
  Proof.
    intros [x sign]. unfold flip. cbn [fst snd]. rewrite !literal_bits.
    destruct sign; cbn [negb]; lia.
  Qed.

  Lemma signed_bits_le : forall x sign, K.bits (x, sign) <= 2 * X.bits x + 1.
  Proof.
    intros x sign. rewrite literal_bits. destruct sign; lia.
  Qed.

  Definition c_octagon : N := (8388608 * (M.c_map + 1) * (M.c_map + 1))%N.

  Lemma T_flip_le : forall i, (T_flip i <= 4)%N.
  Proof.
    intro i. time_step.
  Qed.

  Lemma T_lower_bound_le : forall d old,
    (T_lower_bound d old <= N.of_nat (Z.size_nat d) + 5)%N.
  Proof.
    intros d [z|]; time_step.
  Qed.

  Lemma T_put_le : forall i j d m,
    (T_put i j d m <=
      16 * (M.c_map + 1) * N.of_nat (K.bits i + K.bits j + 1))%N.
  Proof.
    intros i j d m.
    pose proof (M.T_get_le (M.t Z) i m) as Hget.
    pose proof (T_row_of_le (M.get i m)) as Hrow.
    pose proof (M.T_set_le Z j d (row_of (M.get i m))) as Hcolumn.
    pose proof (M.T_set_le (M.t Z) i
      (M.set j d (row_of (M.get i m))) m) as Houter.
    unfold T_put. time_simpl. rewrite !Nat2N.inj_add in *. nia.
  Qed.

  Lemma T_entry_small : forall m i j,
    (T_entry m i j <=
      8 * (M.c_map + 1) * N.of_nat (K.bits i + K.bits j + 1))%N.
  Proof.
    intros m i j. pose proof (M.T_get_le (M.t Z) i m) as Houter.
    unfold T_entry. time_simpl. destruct (M.get i m) as [row|].
    - pose proof (M.T_get_le Z j row) as Hcolumn.
      time_simpl. rewrite !Nat2N.inj_add in *. nia.
    - time_simpl. rewrite !Nat2N.inj_add in *. nia.
  Qed.

  (** Both signed insertions fit one common key-and-payload allowance. *)
  Lemma T_add_cons_small : forall i j d m,
    (T_add_cons i j d m <= 256 * (M.c_map + 1) * N.of_nat
      (K.bits i + K.bits j + Z.size_nat d + 1))%N.
  Proof.
    intros i j d m.
    set (w := N.of_nat (K.bits i + K.bits j + Z.size_nat d + 1)).
    set (c := (M.c_map + 1)%N).
    assert (Hw : (1 <= w)%N) by (unfold w; lia).
    assert (Hc : (1 <= c)%N) by (unfold c; lia).
    assert (Hkeys : (N.of_nat (K.bits i + K.bits j + 1) <= w)%N)
      by (unfold w; lia).
    assert (Hflipped :
      (N.of_nat (K.bits (flip j) + K.bits (flip i) + 1) <= 3 * w)%N).
    { pose proof (flip_bits i). pose proof (flip_bits j). unfold w. lia. }
    assert (Hput : forall z n, (T_put i j z n <= 16 * c * w)%N).
    { intros z n. eapply N.le_trans; [apply T_put_le|].
      fold c. apply N.mul_le_mono_l. exact Hkeys. }
    assert (Hputbar : forall z n, (T_put (flip j) (flip i) z n <= 48 * c * w)%N).
    { intros z n. eapply N.le_trans; [apply T_put_le|]. fold c.
      replace (48 * c * w)%N with (16 * c * (3 * w))%N by ring.
      apply N.mul_le_mono_l. exact Hflipped. }
    assert (Hentry : forall n, (T_entry n i j <= 8 * c * w)%N).
    { intro n. eapply N.le_trans; [apply T_entry_small|].
      fold c. apply N.mul_le_mono_l. exact Hkeys. }
    assert (Hentrybar : forall n, (T_entry n (flip j) (flip i) <= 24 * c * w)%N).
    { intro n. eapply N.le_trans; [apply T_entry_small|]. fold c.
      replace (24 * c * w)%N with (8 * c * (3 * w))%N by ring.
      apply N.mul_le_mono_l. exact Hflipped. }
    assert (Hlower : forall old, (T_lower_bound d old <= 6 * w)%N).
    { intro old. eapply N.le_trans; [apply T_lower_bound_le|]. unfold w. lia. }
    unfold T_add_cons. time_simpl.
    repeat match goal with
    | |- context [T_put i j ?z ?n] =>
      let H := fresh "Hputclock" in pose proof (Hput z n) as H;
      let clock := fresh "clock" in set (clock := T_put i j z n) in *
    | |- context [T_put (flip j) (flip i) ?z ?n] =>
      let H := fresh "Hputclock" in pose proof (Hputbar z n) as H;
      let clock := fresh "clock" in set (clock := T_put (flip j) (flip i) z n) in *
    | |- context [T_entry ?n i j] =>
      let H := fresh "Hentryclock" in pose proof (Hentry n) as H;
      let clock := fresh "clock" in set (clock := T_entry n i j) in *
    | |- context [T_entry ?n (flip j) (flip i)] =>
      let H := fresh "Hentryclock" in pose proof (Hentrybar n) as H;
      let clock := fresh "clock" in set (clock := T_entry n (flip j) (flip i)) in *
    | |- context [T_lower_bound d ?old] =>
      let H := fresh "Hlowerclock" in pose proof (Hlower old) as H;
      let clock := fresh "clock" in set (clock := T_lower_bound d old) in *
    | |- context [T_flip ?k] =>
      let H := fresh "Hflipclock" in pose proof (T_flip_le k) as H;
      let clock := fresh "clock" in set (clock := T_flip k) in *
    end.
    nia.
  Qed.

  Lemma T_entry_le : forall m i j,
    (T_entry m i j <= c_octagon * N.of_nat (K.bits i + K.bits j + 1))%N.
  Proof.
    intros m i j. eapply N.le_trans; [apply T_entry_small|].
    apply N.mul_le_mono_r. unfold c_octagon. nia.
  Qed.
  Lemma T_add_cons_le : forall i j d m,
    (T_add_cons i j d m <= c_octagon * N.of_nat
      (K.bits i + K.bits j + Z.size_nat d + 1))%N.
  Proof.
    intros i j d m. eapply N.le_trans; [apply T_add_cons_small|].
    apply N.mul_le_mono_r. unfold c_octagon. nia.
  Qed.
  Definition coherent (m : dbm) : Prop :=
    forall i j, entry m i j = entry m (bar j) (bar i).
  Definition coh (s : t) : Prop :=
    match s with Unreached => True | Reached m => coherent m end.
  (** The support of a sign-closed matrix holds both signs of each of its keys. *)
  Definition bar_closed (m : dbm) : Prop :=
    forall i, In (K.encode i) (support m) -> In (K.encode (bar i)) (support m).
  Definition same_entries (a b : t) : Prop :=
    match a, b with
    | Reached ma, Reached mb => forall i j, entry ma i j = entry mb i j
    | Unreached, Unreached => True
    | _, _ => False
    end.
  Definition k_octagon : N := (16384 * (M.c_map + 1) * (M.c_map + 1))%N.
  Lemma F_join_entry : forall ma mb i j,
    match join (Reached ma) (Reached mb) with
    | Reached mj => entry mj i j =
        match entry ma i j, entry mb i j with
        | Some x, Some y => Some (Z.max x y)
        | _, _ => None
        end
    | Unreached => False
    end.
  Proof.
    intros ma mb i j. cbn [join].
    change (entry (M.merge row_join ma mb) i j = bound_join (entry ma i j) (entry mb i j)).
    rewrite <- !raw_entry_get. apply raw_entry_join.
  Qed.
  (** Deduplication retains exactly the input and accumulator members. *)
  Lemma dedup_membership : forall (A : Type) (eqb : A -> A -> bool),
    (forall x y, eqb x y = true <-> x = y) -> forall xs acc x,
    In x (fold_left (fun seen y => if existsb (eqb y) seen then seen else y :: seen)
      xs acc) <-> In x xs \/ In x acc.
  Proof.
    intros A eqb Heq xs. induction xs as [|a xs IH]; intros acc x.
    - cbn. tauto.
    - cbn [fold_left]. destruct (existsb (eqb a) acc) eqn:Hseen.
      + assert (Ha : In a acc).
        { apply existsb_exists in Hseen. destruct Hseen as [y [Hy Hay]].
          apply Heq in Hay. now subst y. }
        rewrite IH. cbn [In]. split.
        * tauto.
        * intros [[Hax | Hin] | Hin].
          -- subst x. now right.
          -- now left.
          -- now right.
      + rewrite IH. cbn [In]. tauto.
  Qed.

  (** Deduplication preserves a duplicate-free accumulator. *)
  Lemma dedup_nodup : forall (A : Type) (eqb : A -> A -> bool),
    (forall x y, eqb x y = true <-> x = y) -> forall xs acc,
    NoDup acc ->
    NoDup (fold_left (fun seen y => if existsb (eqb y) seen then seen else y :: seen)
      xs acc).
  Proof.
    intros A eqb Heq xs. induction xs as [|a xs IH]; intros acc Hacc.
    - exact Hacc.
    - cbn [fold_left]. destruct (existsb (eqb a) acc) eqn:Hseen; apply IH.
      + exact Hacc.
      + constructor; [|exact Hacc]. intro Ha.
        assert (Hfound : existsb (eqb a) acc = true).
        { apply existsb_exists. exists a. split; [exact Ha|apply Heq; reflexivity]. }
        congruence.
  Qed.

  (** Support contains every outer code and every code of a stored row. *)
  Lemma support_spec : forall m p,
    In p (support m) <-> In p (M.codes m) \/ In p (flat_map M.codes (rows m)).
  Proof.
    intros m p. unfold support.
    rewrite (dedup_membership positive Pos.eqb Pos.eqb_eq), in_app_iff.
    cbn. tauto.
  Qed.

  (** A list maximum bounds each selected member. *)
  Lemma maximum_member : forall (A : Type) (f : A -> nat) xs x,
    In x xs -> f x <= fold_right Nat.max 0 (map f xs).
  Proof.
    intros A f xs. induction xs as [|a xs IH]; intros x Hin.
    - contradiction.
    - cbn in Hin |- *. destruct Hin as [Hax | Hin].
      + subst x. apply Nat.le_max_l.
      + eapply Nat.le_trans; [exact (IH x Hin)|apply Nat.le_max_r].
  Qed.

  (** A uniform bound on summands bounds their sum by length times that bound. *)
  Lemma sum_members_bound : forall (A : Type) (f : A -> nat) xs upper,
    (forall x, In x xs -> f x <= upper) ->
    fold_right Nat.add 0 (map f xs) <= length xs * upper.
  Proof.
    intros A f xs. induction xs as [|a xs IH]; intros upper Hbound.
    - cbn. lia.
    - cbn. assert (Ha : f a <= upper) by (apply Hbound; now left).
      assert (Htail : fold_right Nat.add 0 (map f xs) <= length xs * upper).
      { apply IH. intros x Hin. apply Hbound. now right. }
      lia.
  Qed.

  (** Every supported code fits the matrix key-bit bound. *)
  Lemma support_bits : forall m p, In p (support m) -> Pos.size_nat p <= b m.
  Proof.
    intros m p Hin. unfold b. now apply maximum_member.
  Qed.

  (** Distinct stored codes inject into any support containing them. *)
  Lemma codes_support_length : forall A (r : M.t A) m,
    (forall p, In p (M.codes r) -> In p (support m)) -> length (M.codes r) <= supp m.
  Proof.
    intros A r m Hin. unfold supp. apply NoDup_incl_length.
    - apply M.codes_nodup.
    - exact Hin.
  Qed.

  (** A map whose codes lie in the support has a bounded skeleton. *)
  Lemma nodes_support : forall A (r : M.t A) m,
    (forall p, In p (M.codes r) -> In p (support m)) ->
    M.nodes r <= supp m * (b m + 1).
  Proof.
    intros A r m Hin.
    pose proof (M.nodes_le_codes A r) as Hnodes.
    pose proof (codes_support_length A r m Hin) as Hlength.
    assert (Hsum : fold_right Nat.add 0
      (map (fun p => Pos.size_nat p + 1) (M.codes r)) <=
      length (M.codes r) * (b m + 1)).
    { apply sum_members_bound. intros p Hp.
      pose proof (support_bits m p (Hin p Hp)). lia. }
    nia.
  Qed.

  (** Row collection retains at most one row for each outer code. *)
  Lemma rows_length : forall m, length (rows m) <= length (M.codes m).
  Proof.
    intro m. unfold rows. induction (M.codes m) as [|p ps IH].
    - reflexivity.
    - cbn. destruct (M.find p m); cbn; lia.
  Qed.

  (** Every successful raw row lookup is present in the row collection. *)
  Lemma row_in_rows : forall m p row, M.find p m = Some row -> In row (rows m).
  Proof.
    intros m p row Hrow. unfold rows. apply in_flat_map. exists p. split.
    - apply M.codes_spec. rewrite Hrow. discriminate.
    - rewrite Hrow. now left.
  Qed.

  (** The stored codes cover the skeleton even when labels do not match their codes. *)
  Lemma skel_le : forall m, skel m <= (supp m + 1)^2 * (b m + 1).
  Proof.
    intro m.
    assert (Houter : forall p, In p (M.codes m) -> In p (support m)).
    { intros p Hp. apply support_spec. now left. }
    pose proof (nodes_support (M.t Z) m m Houter) as Hnodes.
    pose proof (codes_support_length (M.t Z) m m Houter) as Hlength.
    pose proof (rows_length m) as Hrows.
    assert (Hsum : fold_right Nat.add 0 (map M.nodes (rows m)) <=
      length (rows m) * (supp m * (b m + 1))).
    { apply sum_members_bound. intros row Hrow. apply nodes_support.
      intros p Hp. apply support_spec. right. apply in_flat_map.
      exists row. now split. }
    unfold skel. cbn [Nat.pow]. nia.
  Qed.
  (** Raw support and integer-bit bounds use the actual stored codes. *)
  Lemma rows_find : forall m row,
    In row (rows m) <-> exists p, M.find p m = Some row.
  Proof.
    intros m row. split.
    - intro Hin. unfold rows in Hin. apply in_flat_map in Hin.
      destruct Hin as [p [Hp Hin]]. destruct (M.find p m) as [r|] eqn:Hrow.
      + cbn in Hin. destruct Hin as [Heq | Hempty]; [subst r|contradiction].
        now exists p.
      + contradiction.
    - intros [p Hrow]. exact (row_in_rows m p row Hrow).
  Qed.

  (** Support records row codes and column codes independently of their stored labels. *)
  Lemma support_find : forall m p, In p (support m) <->
    M.find p m <> None \/ exists q, raw_entry m q p <> None.
  Proof.
    intros m p. rewrite support_spec. split.
    - intros [Houter | Hinner].
      + left. now apply M.codes_spec.
      + right. apply in_flat_map in Hinner. destruct Hinner as [row [Hrow Hp]].
        apply rows_find in Hrow. destruct Hrow as [q Hrow]. exists q.
        unfold raw_entry. rewrite Hrow. cbn [row_of]. now apply M.codes_spec.
    - intros [Houter | [q Hinner]].
      + left. now apply M.codes_spec.
      + right. unfold raw_entry in Hinner.
        destruct (M.find q m) as [row|] eqn:Hrow; cbn [row_of] in Hinner.
        * apply in_flat_map. exists row. split.
          -- exact (row_in_rows m q row Hrow).
          -- now apply M.codes_spec.
        * rewrite M.find_empty in Hinner. contradiction.
  Qed.

  (** The deduplicated support contains each stored code once. *)
  Lemma support_nodup : forall m, NoDup (support m).
  Proof.
    intro m. unfold support. apply (dedup_nodup positive Pos.eqb Pos.eqb_eq).
    constructor.
  Qed.

  (** A common upper bound for list members bounds their maximum. *)
  Lemma maximum_bound : forall (A : Type) (f : A -> nat) xs upper,
    (forall x, In x xs -> f x <= upper) -> fold_right Nat.max 0 (map f xs) <= upper.
  Proof.
    intros A f xs. induction xs as [|x xs IH]; intros upper Hbound.
    - cbn. lia.
    - cbn. apply Nat.max_lub.
      + apply Hbound. now left.
      + apply IH. intros y Hin. apply Hbound. now right.
  Qed.

  (** Equal support membership gives equal support size and key-bit bounds. *)
  Lemma support_sizes : forall ma mb,
    (forall p, In p (support ma) <-> In p (support mb)) ->
    supp ma = supp mb /\ b ma = b mb.
  Proof.
    intros ma mb Hsame. split.
    - unfold supp. apply Nat.le_antisymm; apply NoDup_incl_length;
        try apply support_nodup.
      + intros p Hin. now apply Hsame.
      + intros p Hin. now apply Hsame.
    - apply Nat.le_antisymm.
      + unfold b at 1. apply maximum_bound. intros p Hin.
        apply support_bits. now apply Hsame.
      + unfold b at 1. apply maximum_bound. intros p Hin.
        apply support_bits. now apply Hsame.
  Qed.


  Lemma maximum_raw_member : forall xs n,
    In n xs -> n <= fold_right Nat.max 0 xs.
  Proof.
    intros xs. induction xs as [|x xs IH]; intros n Hin.
    - contradiction.
    - cbn in Hin. cbn. destruct Hin as [Heq | Hin].
      + subst n. apply Nat.le_max_l.
      + eapply Nat.le_trans; [exact (IH n Hin)|apply Nat.le_max_r].
  Qed.

  (** A uniform upper bound for a list bounds its maximum. *)
  Lemma maximum_raw_bound : forall xs upper,
    (forall n, In n xs -> n <= upper) -> fold_right Nat.max 0 xs <= upper.
  Proof.
    intros xs. induction xs as [|x xs IH]; intros upper Hbound.
    - cbn. lia.
    - cbn. apply Nat.max_lub.
      + apply Hbound. now left.
      + apply IH. intros n Hin. apply Hbound. now right.
  Qed.

  (** Every finite raw entry satisfies the matrix's integer-bit bound. *)
  Lemma ell_entry : forall m p q z,
    raw_entry m p q = Some z -> Z.size_nat z <= ell m.
  Proof.
    intros m p q z Hentry. unfold raw_entry in Hentry.
    destruct (M.find p m) as [row|] eqn:Hrow; cbn [row_of] in Hentry.
    - unfold ell. apply maximum_raw_member. apply in_flat_map.
      exists row. split; [exact (row_in_rows m p row Hrow)|].
      apply in_map_iff. exists q. split.
      + now rewrite Hentry.
      + apply M.codes_spec. rewrite Hentry. discriminate.
    - rewrite M.find_empty in Hentry. discriminate.
  Qed.

  (** Bounding every finite raw entry bounds the matrix's integer-bit maximum. *)
  Lemma ell_bound : forall m upper,
    (forall p q z, raw_entry m p q = Some z -> Z.size_nat z <= upper) ->
    ell m <= upper.
  Proof.
    intros m upper Hbound. unfold ell. apply maximum_raw_bound.
    intros n Hin. apply in_flat_map in Hin. destruct Hin as [row [Hrow Hin]].
    apply in_map_iff in Hin. destruct Hin as [q [Heq Hq]].
    apply rows_find in Hrow. destruct Hrow as [p Hrow].
    destruct (M.find q row) as [z|] eqn:Hentry.
    - subst n. apply (Hbound p q z). unfold raw_entry. rewrite Hrow. exact Hentry.
    - cbn in Heq. lia.
  Qed.

  (** An integer's absolute value fits strictly below its bit-length power of two. *)
  Lemma zbits_upper : forall z, Z.abs_nat z < 2 ^ Z.size_nat z.
  Proof.
    intros [|p|p]; cbn [Z.abs_nat Z.size_nat].
    - change (0 < 1). lia.
    - apply Pos.size_nat_upper.
    - apply Pos.size_nat_upper.
  Qed.

  (** Any strict power-of-two bound also bounds the integer's bit length. *)
  Lemma zbits_least : forall z n,
    Z.abs_nat z < 2 ^ n -> Z.size_nat z <= n.
  Proof.
    intros [|p|p] n Hbound; cbn [Z.abs_nat Z.size_nat] in *.
    - lia.
    - now apply Pos.size_nat_least.
    - now apply Pos.size_nat_least.
  Qed.

  (** Finite range endpoints are bounded by the form and matrix bit allowances. *)
  Lemma zbits_abs_bound : forall z bits,
    Z.size_nat z <= bits -> Z.abs_nat z < 2 ^ bits.
  Proof.
    intros z bits Hbits. eapply Nat.lt_le_trans; [apply zbits_upper|].
    apply Nat.pow_le_mono_r; lia.
  Qed.

  (** The constant seed and every coefficient are bounded by the form maximum. *)
  Lemma form_bits_constant : forall f, Z.size_nat (cst f) <= F.form_bits f.
  Proof.
    intros [cs c]. unfold F.form_bits. cbn [coef cst].
    induction cs as [|p cs IH]; cbn; [lia|].
    eapply Nat.le_trans; [exact IH|apply Nat.le_max_r].
  Qed.

  Lemma form_bits_coefficient : forall f p,
    In p (coef f) -> Z.size_nat (snd p) <= F.form_bits f.
  Proof.
    intros [cs c] p. unfold F.form_bits. cbn [coef cst].
    induction cs as [|q cs IH]; intros Hin; [contradiction|].
    cbn in Hin |- *. destruct Hin as [Heq|Hin].
    - subst q. pose proof (Nat.le_max_l
        (X.bits (fst p) + Z.size_nat (snd p))
        (fold_right Nat.max (Z.size_nat c)
          (map (fun p => X.bits (fst p) + Z.size_nat (snd p)) cs))). lia.
    - eapply Nat.le_trans; [now apply IH|apply Nat.le_max_r].
  Qed.

  (** Negation does not change an integer's stored magnitude. *)
  Lemma zbits_opp : forall z, Z.size_nat (-z)%Z = Z.size_nat z.
  Proof. intros [|p|p]; reflexivity. Qed.

  (** Rounding an integer toward negative infinity while halving cannot enlarge its magnitude. *)
  Lemma zabs_div2_le : forall z, Z.abs_nat (Z.div2 z) <= Z.abs_nat z.
  Proof.
    intro z. apply (proj2 (Nat2Z.inj_le _ _)).
    rewrite !Zabs2Nat.id_abs, Z.div2_div.
    pose proof (Z.div_mod z 2 ltac:(lia)) as Hdiv.
    pose proof (Z.mod_pos_bound z 2 ltac:(lia)) as Hrem.
    destruct (Z.leb_spec0 0 z) as [Hz|Hz].
    - assert (Hq : (0 <= z / 2)%Z) by lia.
      rewrite !Z.abs_eq by lia. lia.
    - assert (Hq : (z / 2 < 0)%Z) by lia.
      rewrite !Z.abs_neq by lia. lia.
  Qed.

  Lemma zbits_div2 : forall z, Z.size_nat (Z.div2 z) <= Z.size_nat z.
  Proof.
    intro z. apply zbits_least.
    eapply Nat.le_lt_trans; [apply zabs_div2_le|apply zbits_upper].
  Qed.

  Lemma variable_bounds_abs : forall m x,
    rel_bounds_abs (2 ^ ell m) (variable_bounds m x).
  Proof.
    intros m x. unfold variable_bounds, rel_bounds_abs, rel_bound_abs.
    destruct (entry m (x, true) (x, false)) as [lo|] eqn:Hlo;
      destruct (entry m (x, false) (x, true)) as [hi|] eqn:Hhi;
      cbn [fst snd]; split; try exact I; apply zbits_abs_bound.
    - rewrite zbits_opp. eapply Nat.le_trans; [apply zbits_div2|].
      eapply ell_entry. rewrite raw_entry_get. exact Hlo.
    - eapply Nat.le_trans; [apply zbits_div2|].
      eapply ell_entry. rewrite raw_entry_get. exact Hhi.
    - rewrite zbits_opp. eapply Nat.le_trans; [apply zbits_div2|].
      eapply ell_entry. rewrite raw_entry_get. exact Hlo.
    - eapply Nat.le_trans; [apply zbits_div2|].
      eapply ell_entry. rewrite raw_entry_get. exact Hhi.
  Qed.

  (** Summing at most n products adds only log2(n) plus one magnitude bit. *)
  Lemma affine_magnitude_allowance : forall count nodes coeff_bits entry_bits,
    count <= nodes -> 1 <= nodes ->
    (count + 1) * 2 ^ coeff_bits * 2 ^ entry_bits <=
      2 ^ (entry_bits + coeff_bits + Nat.log2 nodes + 2).
  Proof.
    intros count nodes coeff_bits entry_bits Hcount Hnodes.
    pose proof (Nat.log2_spec nodes ltac:(lia)) as [_ Hlog].
    assert (Hcountpow : count + 1 <= 2 ^ (Nat.log2 nodes + 1)).
    { replace (Nat.log2 nodes + 1) with (S (Nat.log2 nodes)) by lia. lia. }
    assert (Hproduct : (count + 1) * 2 ^ coeff_bits * 2 ^ entry_bits <=
      2 ^ (Nat.log2 nodes + 1) * 2 ^ coeff_bits * 2 ^ entry_bits).
    { apply Nat.mul_le_mono_r. apply Nat.mul_le_mono_r. exact Hcountpow. }
    eapply Nat.le_trans; [exact Hproduct|].
    rewrite <- !Nat.pow_add_r. apply Nat.pow_le_mono_r; lia.
  Qed.

  (** Recognized affine intervals respect the logarithmic range bit allowance. *)
  Lemma form_range_abs : forall e m f r,
    F.lin_of e = Some (f, r) ->
    rel_bounds_abs (2 ^ range_bits e (Reached m)) (form_bounds m f).
  Proof.
    intros e m f r Hlin. destruct (F.lin_of_size e f r Hlin) as [Hcount Hbits].
    assert (Hposc : 0 < 2 ^ F.bits_e e).
    { pose proof (Nat.pow_nonzero 2 (F.bits_e e) ltac:(lia)). lia. }
    assert (Hposx : 0 < 2 ^ ell m).
    { pose proof (Nat.pow_nonzero 2 (ell m) ltac:(lia)). lia. }
    eapply rel_bounds_abs_mono.
    - unfold range_bits, ells. apply affine_magnitude_allowance; [exact Hcount|].
      destruct e; cbn [tsize]; lia.
    - unfold form_bounds. apply rel_form_bounds_abs; try assumption.
      + apply zbits_abs_bound. pose proof (form_bits_constant f). lia.
      + apply Forall_forall. intros p Hin. apply zbits_abs_bound.
        pose proof (form_bits_coefficient f p Hin). lia.
      + apply variable_bounds_abs.
  Qed.

  (** A valid wrapping interval is bounded by its explicitly charged endpoints. *)
  Lemma wrap_range_abs : forall r bounds bits,
    F.wrap_bits r <= bits -> rel_bounds_abs (2 ^ bits) bounds ->
    rel_bounds_abs (2 ^ bits) (rel_wrap_bounds r bounds).
  Proof.
    intros [|lo hi] bounds bits Hbits Hbounds; [exact Hbounds|].
    unfold F.wrap_bits in Hbits. unfold rel_wrap_bounds.
    destruct (lo <=? hi)%Z; unfold rel_bounds_abs, rel_bound_abs;
      cbn [fst snd]; split; try exact I; apply zbits_abs_bound; lia.
  Qed.

  Lemma range_abs : forall e s,
    rel_bounds_abs (2 ^ range_bits e s) (range e s).
  Proof.
    intros e [|m]; [split; exact I|].
    unfold range. destruct (F.lin_of e) as [[f r]|] eqn:Hlin; [|split; exact I].
    apply wrap_range_abs.
    - destruct (F.lin_of_size e f r Hlin) as [_ Hbits]. unfold range_bits. lia.
    - now apply (form_range_abs e m f r).
  Qed.

  Lemma range_size : forall e s,
    (N.of_nat
      (match fst (range e s) with Fin z => Z.size_nat z | _ => 0 end +
       match snd (range e s) with Fin z => Z.size_nat z | _ => 0 end) <=
     c_num * N.of_nat (range_bits e s + 1))%N.
  Proof.
    intros e s. pose proof (range_abs e s) as Hrange.
    assert (Hbits :
      match fst (range e s) with Fin z => Z.size_nat z | _ => 0 end +
      match snd (range e s) with Fin z => Z.size_nat z | _ => 0 end <=
      2 * range_bits e s).
    { unfold rel_bounds_abs, rel_bound_abs in Hrange.
      destruct (fst (range e s)), (snd (range e s));
        destruct Hrange as [Hlo Hhi]; try apply zbits_least in Hlo;
        try apply zbits_least in Hhi; lia. }
    assert (Hconstant : (2 <= c_num)%N) by (unfold c_num; nia).
    eapply N.le_trans; [apply time_of_nat_le; exact Hbits|].
    rewrite Nat2N.inj_mul. rewrite Nat2N.inj_add. cbn [N.of_nat]. nia.
  Qed.
  (** Adding two integers with a common bit bound needs at most one further bit. *)
  Lemma zbits_add_bound : forall x y upper,
    Z.size_nat x <= upper -> Z.size_nat y <= upper ->
    Z.size_nat (x + y)%Z <= upper + 1.
  Proof.
    intros x y upper Hx Hy.
    pose proof (zbits_upper x) as Hxabs. pose proof (zbits_upper y) as Hyabs.
    assert (Hxp : 2 ^ Z.size_nat x <= 2 ^ upper).
    { apply Nat.pow_le_mono_r; lia. }
    assert (Hyp : 2 ^ Z.size_nat y <= 2 ^ upper).
    { apply Nat.pow_le_mono_r; lia. }
    assert (Htriangle : Z.abs_nat (x + y)%Z <= Z.abs_nat x + Z.abs_nat y).
    { apply (proj2 (Nat2Z.inj_le _ _)).
      rewrite Nat2Z.inj_add, !Zabs2Nat.id_abs. apply Z.abs_triangle. }
    apply zbits_least. replace (upper + 1) with (S upper) by lia.
    cbn [Nat.pow]. lia.
  Qed.

  (** Tightening a bound selects one of its inputs and preserves their common bit bound. *)
  Lemma lower_bound_size : forall d old upper,
    Z.size_nat d <= upper ->
    (forall z, old = Some z -> Z.size_nat z <= upper) ->
    Z.size_nat (lower_bound d old) <= upper.
  Proof.
    intros d [z|] upper Hd Hold; cbn [lower_bound].
    - destruct (Z.leb_spec0 d z) as [Hle | Hgt].
      + now rewrite Z.min_l by exact Hle.
      + rewrite Z.min_r by lia. apply Hold. reflexivity.
    - exact Hd.
  Qed.


  (** Consistent stored labels name codes actually present in their map. *)
  Lemma elements_code : forall A (m : M.t A) k, M.wf m ->
    In k (map fst (M.elements m)) -> In (K.encode k) (M.codes m).
  Proof.
    intros A m k Hwf Hin. apply in_map_iff in Hin.
    destruct Hin as [[q value] [Hq Hin]]. cbn in Hq. subst q.
    apply M.codes_spec. rewrite <- (M.get_find A k m).
    pose proof (proj1 (M.elements_spec A m k value Hwf) Hin) as Hget.
    rewrite Hget. discriminate.
  Qed.

  (** Injective encoding preserves distinct pivot keys. *)
  Lemma encoded_keys_nodup : forall ks, NoDup ks -> NoDup (map K.encode ks).
  Proof.
    intros ks Hkeys. induction Hkeys as [|k ks Hfresh Hkeys IH].
    - constructor.
    - cbn. constructor; [|exact IH]. intro Hin. apply in_map_iff in Hin.
      destruct Hin as [q [Hcode Hq]]. apply K.encode_inj in Hcode.
      subst q. exact (Hfresh Hq).
  Qed.
  (** This proof abbreviation names the row merge already used by a Floyd-Warshall round. *)
  Local Definition relax_round (k : K.t) (m : dbm) : dbm :=
    M.merge (round_row k (row_of (M.get k m))) m M.empty.

  Lemma find_put_presence : forall i j d m p,
    M.find p (put i j d m) <> None <-> p = K.encode i \/ M.find p m <> None.
  Proof.
    intros i j d m p. unfold put. rewrite M.find_set.
    destruct (Pos.eqb p (K.encode i)) eqn:Hkey.
    - apply Pos.eqb_eq in Hkey. subst p. split; [intros; now left|intros; discriminate].
    - apply Pos.eqb_neq in Hkey. tauto.
  Qed.

  (** Constraint insertion changes finite-entry presence only at its supplied coordinates. *)
  Lemma raw_put_presence : forall i j d m p q,
    raw_entry (put i j d m) p q <> None <->
    (p = K.encode i /\ q = K.encode j) \/ raw_entry m p q <> None.
  Proof.
    intros i j d m p q. unfold raw_entry, put. rewrite M.find_set.
    destruct (Pos.eqb p (K.encode i)) eqn:Hrow.
    - apply Pos.eqb_eq in Hrow. subst p. cbn [row_of]. rewrite M.find_set.
      destruct (Pos.eqb q (K.encode j)) eqn:Hcol.
      + apply Pos.eqb_eq in Hcol. subst q. split.
        * intros. left. now split.
        * intros. discriminate.
      + apply Pos.eqb_neq in Hcol. rewrite M.get_find. tauto.
    - apply Pos.eqb_neq in Hrow. tauto.
  Qed.

  (** Insertion adds only its two endpoint codes to the support. *)
  Lemma support_put : forall i j d m p,
    In p (support (put i j d m)) <->
    p = K.encode i \/ p = K.encode j \/ In p (support m).
  Proof.
    intros i j d m p. split.
    - intro Hin. apply support_find in Hin. destruct Hin as [Hrow | [q Hentry]].
      + apply find_put_presence in Hrow. destruct Hrow as [Heq | Hrow].
        * now left.
        * right. right. apply support_find. now left.
      + apply raw_put_presence in Hentry. destruct Hentry as [[Hq Hp] | Hentry].
        * right. now left.
        * right. right. apply support_find. right. now exists q.
    - intros [Hrow | [Hcol | Hin]]; apply support_find.
      + left. apply find_put_presence. now left.
      + right. exists (K.encode i). apply raw_put_presence. left. now split.
      + apply support_find in Hin. destruct Hin as [Hrow | [q Hentry]].
        * left. apply find_put_presence. now right.
        * right. exists q. apply raw_put_presence. now right.
  Qed.

  (** The pivot test recognizes precisely the supplied key's membership in raw support. *)
  Lemma pivot_present_support : forall k m,
    pivot_present k m = true <-> In (K.encode k) (support m).
  Proof.
    intros k m. unfold pivot_present. rewrite M.get_find.
    destruct (M.find (K.encode k) m) as [row|] eqn:Hrow.
    - split; [intros|reflexivity]. apply support_find. left. rewrite Hrow. discriminate.
    - rewrite (M.existsb_spec (M.t Z) (column_present k) m). split.
      + intros [p [row [Hp Hcol]]]. apply support_find. right. exists p.
        unfold raw_entry. rewrite Hp. cbn [row_of].
        unfold column_present in Hcol. rewrite M.get_find in Hcol.
        destruct (M.find (K.encode k) row); congruence.
      + intro Hin. apply support_find in Hin. destruct Hin as [Hfound | [p Hentry]].
        * rewrite Hrow in Hfound. contradiction.
        * unfold raw_entry in Hentry. destruct (M.find p m) as [r|] eqn:Hp.
          -- exists p, r. split; [exact Hp|]. unfold column_present. rewrite M.get_find.
             cbn [row_of] in Hentry. destruct (M.find (K.encode k) r); congruence.
          -- cbn [row_of] in Hentry. rewrite M.find_empty in Hentry. contradiction.
  Qed.

  (** Relaxation retains precisely the existing outer rows. *)
  Lemma find_relax_presence : forall k m p,
    M.find p (relax_round k m) <> None <-> M.find p m <> None.
  Proof.
    intros k m p. unfold relax_round. rewrite M.find_merge by reflexivity.
    rewrite M.find_empty. destruct (M.find p m); cbn [round_row]; split; congruence.
  Qed.

  (** A relaxed coordinate is old or joins an incoming and an outgoing pivot edge. *)
  Lemma raw_relax_presence : forall k m p q,
    raw_entry (relax_round k m) p q <> None <->
    raw_entry m p q <> None \/
      (raw_entry m p (K.encode k) <> None /\ raw_entry m (K.encode k) q <> None).
  Proof.
    intros k m p q. unfold raw_entry, relax_round.
    rewrite M.find_merge by reflexivity. rewrite M.find_empty.
    destruct (M.find p m) as [row|] eqn:Hrow; cbn [round_row relax_row row_of].
    - rewrite !M.get_find. destruct (M.find (K.encode k) row) as [a|] eqn:Hentry;
        cbn [relax_row].
      + rewrite M.find_merge by reflexivity.
        destruct (M.find q row), (M.find q (row_of (M.find (K.encode k) m)));
          cbn [via_bound]; intuition congruence.
      + tauto.
    - rewrite !M.find_empty. tauto.
  Qed.

  (** Relaxing through a pivot adds no code and deletes no supported code. *)
  Lemma support_relax : forall k m p,
    In p (support (relax_round k m)) <-> In p (support m).
  Proof.
    intros k m p. rewrite !support_find. split.
    - intros [Hrow | [q Hentry]].
      + left. now apply find_relax_presence in Hrow.
      + apply raw_relax_presence in Hentry. right.
        destruct Hentry as [Hentry | [Hprefix Hsuffix]].
        * now exists q.
        * now exists (K.encode k).
    - intros [Hrow | [q Hentry]].
      + left. now apply find_relax_presence.
      + right. exists q. apply raw_relax_presence. now left.
  Qed.

  (** Materializing an already-supported pivot diagonal leaves support unchanged. *)
  Lemma support_round : forall k m p,
    In p (support (fw_round k m)) <-> In p (support m).
  Proof.
    intros k m p. unfold fw_round.
    change (In p (support (relax_round k
      (if pivot_present k m then put k k (lower_bound 0%Z (entry m k k)) m else m))) <->
      In p (support m)).
    rewrite support_relax.
    destruct (pivot_present k m) eqn:Hpresent; [|reflexivity].
    apply pivot_present_support in Hpresent. rewrite support_put.
    split.
    - intros [Heq | [Heq | Hin]]; subst; assumption.
    - intro Hin. right. now right.
  Qed.


  (** A raw update changes exactly its supplied coordinate. *)
  Lemma raw_entry_put : forall i j d m p q,
    raw_entry (put i j d m) p q =
    if Pos.eqb p (K.encode i) then
      if Pos.eqb q (K.encode j) then Some d else raw_entry m p q
    else raw_entry m p q.
  Proof.
    intros i j d m p q. unfold raw_entry, put. rewrite M.find_set.
    destruct (Pos.eqb p (K.encode i)) eqn:Hrow; [|reflexivity].
    apply Pos.eqb_eq in Hrow. subst p. cbn [row_of]. rewrite M.find_set.
    destruct (Pos.eqb q (K.encode j)); [reflexivity|]. now rewrite M.get_find.
  Qed.

  Lemma ell_put : forall i j d m upper,
    ell m <= upper -> Z.size_nat d <= upper -> ell (put i j d m) <= upper.
  Proof.
    intros i j d m upper Hm Hd. apply ell_bound. intros p q z Hentry.
    rewrite raw_entry_put in Hentry.
    destruct (Pos.eqb p (K.encode i)).
    - destruct (Pos.eqb q (K.encode j)).
      + injection Hentry as <-. exact Hd.
      + eapply Nat.le_trans; [eapply ell_entry; exact Hentry|exact Hm].
    - eapply Nat.le_trans; [eapply ell_entry; exact Hentry|exact Hm].
  Qed.

  Lemma lower_bound_ell : forall m i j d upper,
    ell m <= upper -> Z.size_nat d <= upper ->
    Z.size_nat (lower_bound d (entry m i j)) <= upper.
  Proof.
    intros m i j d upper Hm Hd. apply lower_bound_size; [exact Hd|].
    intros z Hz. eapply Nat.le_trans; [|exact Hm].
    eapply ell_entry. rewrite raw_entry_get. exact Hz.
  Qed.

  (** Inserting signed twins preserves a common bit allowance for the old and new bounds. *)
  Lemma ell_add_cons : forall i j d m upper,
    ell m <= upper -> Z.size_nat d <= upper -> ell (add_cons i j d m) <= upper.
  Proof.
    intros i j d m upper Hm Hd. unfold add_cons. apply ell_put.
    - apply ell_put; [exact Hm|]. now apply lower_bound_ell.
    - now apply lower_bound_ell.
  Qed.

  Lemma raw_entry_relax : forall k m p q,
    raw_entry (relax_round k m) p q =
    match raw_entry m p (K.encode k) with
    | Some a => via_bound a (raw_entry m p q) (raw_entry m (K.encode k) q)
    | None => raw_entry m p q
    end.
  Proof.
    intros k m p q. unfold raw_entry, relax_round.
    rewrite M.find_merge by reflexivity. rewrite M.find_empty.
    destruct (M.find p m) as [row|]; cbn [round_row relax_row row_of].
    - rewrite !M.get_find. destruct (M.find (K.encode k) row); cbn [relax_row].
      + now rewrite M.find_merge by reflexivity.
      + reflexivity.
    - now rewrite !M.find_empty.
  Qed.

  (** One sparse relaxation adds at most one bit to the maximum stored bound. *)
  Lemma ell_relax : forall k m, ell (relax_round k m) <= ell m + 1.
  Proof.
    intros k m. apply ell_bound. intros p q z Hentry.
    rewrite raw_entry_relax in Hentry.
    destruct (raw_entry m p (K.encode k)) as [a|] eqn:Ha.
    - unfold via_bound in Hentry.
      destruct (raw_entry m (K.encode k) q) as [c|] eqn:Hc.
      + injection Hentry as <-. apply lower_bound_size.
        * apply zbits_add_bound; [exact (ell_entry m p (K.encode k) a Ha)|
            exact (ell_entry m (K.encode k) q c Hc)].
        * intros old Hold. pose proof (ell_entry m p q old Hold). lia.
      + pose proof (ell_entry m p q z Hentry). lia.
    - pose proof (ell_entry m p q z Hentry). lia.
  Qed.
  Lemma weight_le : forall m, dbm_wf m -> M.weight m <= supp m * (b m + 1).
  Proof.
    intros m [Houter Hrows].
    assert (Hkeys : forall k, In k (map fst (M.elements m)) ->
      In (K.encode k) (support m)).
    { intros k Hin. apply support_spec. left. now apply elements_code. }
    assert (Hlength : length (M.elements m) <= supp m).
    { unfold supp.
      rewrite <- (length_map fst (M.elements m)).
      rewrite <- (length_map K.encode (map fst (M.elements m))).
      apply NoDup_incl_length.
      - apply encoded_keys_nodup. now apply M.elements_nodup.
      - intros p Hin. apply in_map_iff in Hin. destruct Hin as [k [Heq Hin]].
        subst p. now apply Hkeys. }
    assert (Hsum : fold_right Nat.add 0
      (map (fun kv => Pos.size_nat (K.encode (fst kv)) + 1) (M.elements m)) <=
      length (M.elements m) * (b m + 1)).
    { apply sum_members_bound. intros [k row] Hin. cbn [fst].
      assert (Hkey : In (K.encode k) (support m)).
      { apply Hkeys. apply in_map_iff. exists (k, row). now split. }
      pose proof (support_bits m (K.encode k) Hkey). lia. }
    unfold M.weight. nia.
  Qed.

  (** Widening units cover the squared support size. *)
  Lemma F_wunits : forall s, wunits s = (ns s + 1) ^ 2.
  Proof.
    reflexivity.
  Qed.
  (** Assumption work charges incremental closure for every emitted atom. *)
  Lemma F_assume_work : forall g es s,
    (N.of_nat (assume_work g es s) =
      N.of_nat (length (F.atoms_of g es) *
        (ns s + 2 * length (F.atoms_of g es) + 1)^2 *
        (bs s + ells s + F.bits_es g es + 2 * length (F.atoms_of g es) + 1) +
        length (F.atoms_of g es) * labs s) +
      F.T_atoms_of g es)%N.
  Proof.
    intros g es s. unfold assume_work. rewrite Nat2N.inj_add, N2Nat.id. reflexivity.
  Qed.
  (** Assignment work pays for linearization and quadratic matrix updates. *)
  Lemma F_assign_work : forall x e s,
    (N.of_nat (assign_work x e s) =
      N.of_nat ((ns s + 1)^2 *
        (bs s + ells s + X.bits x + F.bits_e e + lin_bits e + 1) + skels s + labs s +
        (tsize e + 1) * (bs s + ells s + F.bits_e e + Nat.log2 (tsize e) + 1)^2) +
      F.T_lin_of e)%N.
  Proof.
    intros x e s. unfold assign_work. rewrite Nat2N.inj_add, N2Nat.id. reflexivity.
  Qed.
  Lemma F_havoc_work : forall x s,
    havoc_work x s = (ns s + 1)^2 * (bs s + X.bits x + ells s + 1) + skels s.
  Proof.
    reflexivity.
  Qed.
  Lemma coh_top : coh top.
  Proof.
    intros i j. unfold entry. now rewrite !M.get_empty.
  Qed.
  Lemma coh_join : forall a b, coh a -> coh b -> coh (join a b).
  Proof.
    intros [|ma] [|mb] Ha Hb; cbn [coh join] in *; try assumption; try exact I.
    intros i j. rewrite <- !raw_entry_get, !raw_entry_join, !raw_entry_get.
    now rewrite (Ha i j), (Hb i j).
  Qed.
  Lemma coh_widen : forall p a b, coh a -> coh b -> coh (widen p a b).
  Proof.
    intros p a b Ha Hb. unfold widen. destruct (leb b a); [exact Ha|].
    destruct a as [|ma], b as [|mb]; cbn [coh] in *; try assumption; try exact I.
    intros i j. rewrite <- !raw_entry_get, !raw_entry_widen, !raw_entry_get.
    now rewrite (Ha i j), (Hb i j).
  Qed.
  Lemma coh_havoc : forall x s, coh s -> coh (havoc x s).
  Proof.
    intros x [|m] Hcoh; [exact I|]. intros i j.
    rewrite !entry_havoc. cbn [bar fst snd].
    destruct (X.eqb (fst i) x), (X.eqb (fst j) x); try reflexivity.
    apply Hcoh.
  Qed.
  (** Retrieving a row, with an empty fallback, preserves map consistency. *)
  Lemma row_of_wf : forall m k,
    dbm_wf m -> M.wf (row_of (M.get k m)).
  Proof.
    intros m k [_ Hrows]. rewrite M.get_find.
    destruct (M.find (K.encode k) m) as [row|] eqn:Hrow; cbn [row_of].
    - exact (Hrows (K.encode k) row Hrow).
    - apply M.wf_empty.
  Qed.

  Lemma dbm_empty_wf : dbm_wf M.empty.
  Proof.
    split; [apply M.wf_empty|]. intros p row Hrow.
    rewrite M.find_empty in Hrow. discriminate Hrow.
  Qed.

  (** Inserting a consistent row preserves consistency of the matrix. *)
  Lemma dbm_set_wf : forall k row m,
    dbm_wf m -> M.wf row -> dbm_wf (M.set k row m).
  Proof.
    intros k row m [Houter Hrows] Hrow. split.
    - now apply M.wf_set.
    - intros p next Hnext. rewrite M.find_set in Hnext.
      destruct (Pos.eqb p (K.encode k)).
      + injection Hnext as <-. exact Hrow.
      + exact (Hrows p next Hnext).
  Qed.

  (** A row-wise update preserves consistency when every returned row does. *)
  Lemma dbm_merge_wf : forall
      (f : option (M.t Z) -> option (M.t Z) -> option (M.t Z)) m,
    f None None = None -> dbm_wf m ->
    (forall old row, M.wf old -> f (Some old) None = Some row -> M.wf row) ->
    dbm_wf (M.merge f m M.empty).
  Proof.
    intros f m Hnone [Houter Hrows] Hf. split.
    - apply M.wf_merge; [exact Houter|apply M.wf_empty].
    - intros p row Hrow. rewrite M.find_merge in Hrow by exact Hnone.
      rewrite M.find_empty in Hrow.
      destruct (M.find p m) as [old|] eqn:Hold.
      + eapply Hf; [exact (Hrows p old Hold)|exact Hrow].
      + rewrite Hnone in Hrow. discriminate Hrow.
  Qed.

  (** Replacing rows from another consistent matrix retains consistent labels. *)
  Lemma replace_wf : forall m fresh,
    dbm_wf m -> dbm_wf fresh -> dbm_wf (M.merge replace_row m fresh).
  Proof.
    intros m fresh [Houter Hrows] [Hfresh Hnexts]. split.
    - now apply M.wf_merge.
    - intros p row Hrow. rewrite M.find_merge in Hrow by reflexivity.
      destruct (M.find p m) as [old|] eqn:Hold; cbn [replace_row] in Hrow.
      + destruct (M.find p fresh) as [next|] eqn:Hnext; injection Hrow as <-.
        * exact (Hnexts p next Hnext).
        * exact (Hrows p old Hold).
      + discriminate Hrow.
  Qed.

  Lemma put_wf : forall i j d m, dbm_wf m -> dbm_wf (put i j d m).
  Proof.
    intros i j d m Hwf. unfold put. apply dbm_set_wf; [exact Hwf|].
    apply M.wf_set. now apply row_of_wf.
  Qed.

  Lemma add_cons_wf : forall i j d m, dbm_wf m -> dbm_wf (add_cons i j d m).
  Proof.
    intros i j d m Hwf. unfold add_cons. now apply put_wf, put_wf.
  Qed.

  Lemma relax_row_wf : forall prefix row exit,
    M.wf row -> M.wf exit -> M.wf (relax_row prefix row exit).
  Proof.
    intros [a|] row exit Hrow Hexit; cbn [relax_row]; [now apply M.wf_merge|exact Hrow].
  Qed.

  Lemma round_merge_wf : forall k m, dbm_wf m ->
    dbm_wf (M.merge (round_row k (row_of (M.get k m))) m M.empty).
  Proof.
    intros k m Hwf. apply dbm_merge_wf; [reflexivity|exact Hwf|].
    intros old row Hold Hrow. cbn [round_row] in Hrow. injection Hrow as <-.
    apply relax_row_wf; [exact Hold|now apply row_of_wf].
  Qed.

  Lemma round_wf : forall k m, dbm_wf m -> dbm_wf (fw_round k m).
  Proof.
    intros k m Hwf. unfold fw_round. apply round_merge_wf.
    destruct (pivot_present k m); [now apply put_wf|exact Hwf].
  Qed.

  Lemma fw_pivots_wf : forall ks m, dbm_wf m -> dbm_wf (fw_pivots ks m).
  Proof.
    intro ks. induction ks as [|k ks IH]; intros m Hwf; cbn [fw_pivots].
    - exact Hwf.
    - destruct (nonnegative k (fw_round k m)); [apply IH|]; now apply round_wf.
  Qed.

  Lemma tighten_row_wf : forall m changed k ignored,
    dbm_wf m -> dbm_wf changed -> dbm_wf (tighten_row m changed k ignored).
  Proof.
    intros m changed k ignored Hwf Hchanged. unfold tighten_row.
    destruct (M.get k changed); [exact Hchanged|].
    destruct (M.get k m) as [row|] eqn:Hrow; [|exact Hchanged].
    destruct (M.get (flip k) row); [|exact Hchanged].
    apply dbm_set_wf; [exact Hchanged|]. apply M.wf_set.
    destruct Hwf as [_ Hrows]. rewrite M.get_find in Hrow.
    exact (Hrows (K.encode k) row Hrow).
  Qed.

  Lemma tighten_wf : forall m, dbm_wf m -> dbm_wf (tighten m).
  Proof.
    intros m Hwf. unfold tighten. apply replace_wf; [exact Hwf|].
    apply (fold_invariant _ _ dbm_wf); [apply dbm_empty_wf|].
    intros changed k ignored Hchanged. now apply tighten_row_wf.
  Qed.

  Lemma strengthen_wf : forall m, dbm_wf m -> dbm_wf (strengthen m).
  Proof.
    intros m [Houter Hrows]. unfold strengthen.
    remember (M.fold (unary_maps m) m (M.empty, M.empty)) as unaries eqn:Hunaries.
    pose proof (collect_unary_wf m) as Hwf. rewrite <- Hunaries in Hwf.
    destruct Hwf as [Hleft Hright]. split.
    - now apply M.wf_merge.
    - intros p row Hrow. rewrite M.find_merge in Hrow by reflexivity.
      destruct (M.find p m) as [old|] eqn:Hold; cbn [strengthen_outer] in Hrow;
        [|discriminate Hrow].
      destruct (M.find p (fst unaries)) as [a|]; injection Hrow as <-.
      + apply M.wf_merge; [exact (Hrows p old Hold)|exact Hright].
      + exact (Hrows p old Hold).
  Qed.

  Lemma increment_wf : forall i j d m, dbm_wf m ->
    dbm_wf (M.merge
      (increment_row i j d (row_of (M.get j m)) (row_of (M.get (flip i) m))
        (entry m j (flip j)) (entry m (flip i) i)) m M.empty).
  Proof.
    intros i j d m Hwf. apply dbm_merge_wf; [reflexivity|exact Hwf|].
    intros old row Hold Hrow. cbn [increment_row] in Hrow. injection Hrow as <-.
    apply relax_row_wf; [|now apply row_of_wf].
    apply relax_row_wf; [|now apply row_of_wf].
    apply relax_row_wf; [|now apply row_of_wf].
    apply relax_row_wf; [exact Hold|now apply row_of_wf].
  Qed.

  Lemma wf_add_cons : forall i j d m, dbm_wf m -> dbm_wf (add_cons i j d m).
  Proof.
    exact add_cons_wf.
  Qed.
  Lemma wf_incr_close : forall i j d m, dbm_wf m ->
    match incr_close i j d m with Unreached => True | Reached m' => dbm_wf m' end.
  Proof.
    intros i j d m Hwf. unfold incr_close.
    set (seed := add_cons j j 0%Z (add_cons i i 0%Z m)).
    set (next := M.merge
      (increment_row i j d (row_of (M.get j seed)) (row_of (M.get (flip i) seed))
        (entry seed j (flip j)) (entry seed (flip i) i)) seed M.empty).
    destruct (matrix_ok next); [|exact I].
    destruct (matrix_ok (strengthen (tighten next))); [|exact I].
    apply strengthen_wf, tighten_wf. unfold next. apply increment_wf. unfold seed.
    now apply add_cons_wf, add_cons_wf.
  Qed.
  Lemma wf_fw_round : forall k m, dbm_wf m -> dbm_wf (fw_round k m).
  Proof.
    exact round_wf.
  Qed.
  (** Replacing one raw row preserves any common payload-bit allowance. *)
  Lemma ell_set_row : forall m k row upper,
    ell m <= upper ->
    (forall q z, M.find q row = Some z -> Z.size_nat z <= upper) ->
    ell (M.set k row m) <= upper.
  Proof.
    intros m k row upper Hm Hrow. apply ell_bound. intros p q z Hentry.
    unfold raw_entry in Hentry. rewrite M.find_set in Hentry.
    destruct (Pos.eqb p (K.encode k)); cbn [row_of] in Hentry.
    - now apply (Hrow q z).
    - eapply Nat.le_trans; [eapply ell_entry; exact Hentry|exact Hm].
  Qed.

  (** Choosing old or replacement rows preserves their common bit bound. *)
  Lemma ell_replace_rows : forall m changed upper,
    ell m <= upper -> ell changed <= upper ->
    ell (M.merge replace_row m changed) <= upper.
  Proof.
    intros m changed upper Hm Hchanged. apply ell_bound. intros p q z Hentry.
    unfold raw_entry in Hentry. rewrite M.find_merge in Hentry by reflexivity.
    destruct (M.find p m) as [row|] eqn:Hrow; cbn [replace_row row_of] in Hentry.
    - destruct (M.find p changed) as [fresh|] eqn:Hfresh;
        cbn [row_of] in Hentry.
      + eapply Nat.le_trans; [eapply (ell_entry changed p q z)|exact Hchanged].
        unfold raw_entry. now rewrite Hfresh.
      + eapply Nat.le_trans; [eapply (ell_entry m p q z)|exact Hm].
        unfold raw_entry. now rewrite Hrow.
    - rewrite M.find_empty in Hentry. discriminate.
  Qed.

  (** Rounding a unary bound down to an even integer costs at most one bit. *)
  Lemma even_bound_bits : forall d,
    Z.size_nat (even_bound d) <= Z.size_nat d + 1.
  Proof.
    intro d. unfold even_bound.
    replace (2 * Z.div2 d)%Z with (Z.div2 d + Z.div2 d)%Z by ring.
    apply zbits_add_bound; apply zbits_div2.
  Qed.

  Lemma tighten_row_bits : forall m changed k ignored,
    ell changed <= ell m + 1 -> ell (tighten_row m changed k ignored) <= ell m + 1.
  Proof.
    intros m changed k ignored Hchanged. unfold tighten_row.
    destruct (M.get k changed); [exact Hchanged|].
    destruct (M.get k m) as [row|] eqn:Hrow; [|exact Hchanged].
    destruct (M.get (flip k) row) as [d|] eqn:Hbound; [|exact Hchanged].
    apply ell_set_row; [exact Hchanged|]. intros q z Hentry.
    rewrite M.find_set in Hentry.
    destruct (Pos.eqb q (K.encode (flip k))) eqn:Hkey.
    - injection Hentry as <-. eapply Nat.le_trans; [apply even_bound_bits|].
      assert (Hd : Z.size_nat d <= ell m).
      { eapply (ell_entry m (K.encode k) (K.encode (flip k)) d).
        unfold raw_entry. rewrite <- (M.get_find (M.t Z) k m), Hrow. cbn [row_of].
        now rewrite <- (M.get_find Z (flip k) row). }
      lia.
    - assert (Hz : Z.size_nat z <= ell m).
      { eapply (ell_entry m (K.encode k) q z).
        unfold raw_entry. rewrite <- (M.get_find (M.t Z) k m), Hrow. exact Hentry. }
      lia.
  Qed.

  (** Unary collection retains the source lookup of every stored payload. *)
  Definition unary_origins (m : dbm) (acc : M.t Z * M.t Z) : Prop :=
    (forall p d, M.find p (fst acc) = Some d ->
      exists k, p = K.encode k /\ entry m k (flip k) = Some d) /\
    (forall p d, M.find p (snd acc) = Some d ->
      exists k, p = K.encode (flip k) /\ entry m k (flip k) = Some d).

  Lemma unary_maps_origins : forall m acc k ignored,
    unary_origins m acc -> unary_origins m (unary_maps m acc k ignored).
  Proof.
    intros m acc k ignored [Hleft Hright]. unfold unary_maps.
    destruct (entry m k (flip k)) as [d|] eqn:Hsource; [|now split].
    split; intros p z Hentry; cbn [fst snd] in Hentry;
      rewrite M.find_set in Hentry.
    - destruct (Pos.eqb p (K.encode k)) eqn:Hkey.
      + apply Pos.eqb_eq in Hkey. injection Hentry as <-.
        exists k. now split.
      + now apply Hleft.
    - destruct (Pos.eqb p (K.encode (flip k))) eqn:Hkey.
      + apply Pos.eqb_eq in Hkey. injection Hentry as <-.
        exists k. now split.
      + now apply Hright.
  Qed.

  Lemma collect_unary_origins : forall m,
    unary_origins m (M.fold (unary_maps m) m (M.empty, M.empty)).
  Proof.
    intro m. apply (fold_invariant _ _ (unary_origins m)).
    - split; intros p d Hentry; cbn [fst snd] in Hentry;
        rewrite M.find_empty in Hentry; discriminate.
    - intros acc k ignored Hacc. now apply unary_maps_origins.
  Qed.

  (** An integer average stays within the common bit bound of its operands. *)
  Lemma average_bits : forall a b upper,
    Z.size_nat a <= upper -> Z.size_nat b <= upper ->
    Z.size_nat (Z.div2 (a + b)) <= upper.
  Proof.
    intros a b upper Ha Hb. apply zbits_least.
    pose proof (zbits_abs_bound a upper Ha) as HabsA.
    pose proof (zbits_abs_bound b upper Hb) as HabsB.
    assert (HA : (Z.abs a < Z.of_nat (2 ^ upper))%Z).
    { rewrite <- Zabs2Nat.id_abs. lia. }
    assert (HB : (Z.abs b < Z.of_nat (2 ^ upper))%Z).
    { rewrite <- Zabs2Nat.id_abs. lia. }
    apply Z.abs_lt in HA. apply Z.abs_lt in HB.
    apply (proj2 (Nat2Z.inj_lt _ _)).
    rewrite Zabs2Nat.id_abs, Z.div2_div. apply Z.abs_lt.
    pose proof (Z.div_mod (a + b) 2 ltac:(lia)) as Hdiv.
    pose proof (Z.mod_pos_bound (a + b) 2 ltac:(lia)) as Hrem.
    lia.
  Qed.

  (** Strengthening averages validated unary bounds and never enlarges the payload maximum. *)
  Lemma bits_strengthen_le : forall m, ell (strengthen m) <= ell m.
  Proof.
    intro m. unfold strengthen.
    remember (M.fold (unary_maps m) m (M.empty, M.empty)) as unaries eqn:Hunaries.
    pose proof (collect_unary_origins m) as Horigins.
    rewrite <- Hunaries in Horigins. destruct Horigins as [Hleft Hright].
    apply ell_bound. intros p q z Hentry.
    unfold raw_entry in Hentry. rewrite M.find_merge in Hentry by reflexivity.
    destruct (M.find p m) as [row|] eqn:Hrow; cbn [strengthen_outer row_of] in Hentry.
    - assert (Hold : forall d, M.find q row = Some d -> Z.size_nat d <= ell m).
      { intros d Hd. eapply (ell_entry m p q d). unfold raw_entry. now rewrite Hrow. }
      destruct (M.find p (fst unaries)) as [a|] eqn:Ha.
      + rewrite M.find_merge in Hentry by reflexivity.
        unfold strengthen_bound in Hentry.
        destruct (M.find q (snd unaries)) as [b|] eqn:Hb.
        * injection Hentry as <-. apply lower_bound_size; [|exact Hold].
          destruct (Hleft p a Ha) as [i [Hi Hai]].
          destruct (Hright q b Hb) as [j [Hj Hbj]].
          apply average_bits.
          -- eapply ell_entry. rewrite raw_entry_get. exact Hai.
          -- eapply ell_entry. rewrite raw_entry_get. exact Hbj.
        * now apply Hold.
      + now apply Hold.
    - rewrite M.find_empty in Hentry. discriminate.
  Qed.

  (** Tightening and strengthening preserve all original outer labels. *)
  Lemma weight_tighten : forall m, M.weight (tighten m) <= M.weight m.
  Proof.
    intro m. unfold tighten. apply M.weight_merge_l. reflexivity.
  Qed.

  Lemma weight_strengthen : forall m, M.weight (strengthen m) <= M.weight m.
  Proof.
    intro m. unfold strengthen. apply M.weight_merge_l. reflexivity.
  Qed.


  Lemma bits_tighten_le : forall m, ell (tighten m) <= ell m + 1.
  Proof.
    intro m. unfold tighten. apply ell_replace_rows; [lia|].
    apply (fold_invariant _ _ (fun changed => ell changed <= ell m + 1)).
    - apply ell_bound. intros p q z Hentry. unfold raw_entry in Hentry.
      rewrite M.find_empty in Hentry. cbn [row_of] in Hentry.
      rewrite M.find_empty in Hentry. discriminate.
    - intros changed k ignored Hchanged. now apply tighten_row_bits.
  Qed.
  Definition strongly_closed (m : dbm) : Prop :=
    coherent m /\
    (forall i, In (K.encode i) (support m) -> entry m i i = Some 0%Z) /\
    (forall i j k a z, entry m i k = Some a -> entry m k j = Some z ->
      exists d, entry m i j = Some d /\ (d <= a + z)%Z) /\
    (forall i j a z, entry m i (bar i) = Some a -> entry m (bar j) j = Some z ->
      exists d, entry m i j = Some d /\ (2 * d <= a + z)%Z).
  Definition tightly_closed (m : dbm) : Prop := strongly_closed m /\
    (forall i d, entry m i (bar i) = Some d -> (d mod 2 = 0)%Z).
  Lemma fw_implied : forall m v, models m v -> models (fw m) v.
  Proof.
    exact fw_models.
  Qed.
  Lemma strengthen_implied : forall m v, models m v -> models (strengthen m) v.
  Proof.
    exact strengthen_models.
  Qed.
  Lemma tighten_implied : forall m v, models m v -> models (tighten m) v.
  Proof.
    exact tighten_models.
  Qed.
  Lemma wf_fw : forall m, dbm_wf m -> dbm_wf (fw m).
  Proof.
    intros m Hwf. unfold fw. now apply fw_pivots_wf.
  Qed.
  Lemma wf_tighten : forall m, dbm_wf m -> dbm_wf (tighten m).
  Proof.
    exact tighten_wf.
  Qed.
  Lemma wf_strengthen : forall m, dbm_wf m -> dbm_wf (strengthen m).
  Proof.
    exact strengthen_wf.
  Qed.
  Lemma tclose_sound : forall m v, models m v -> ngamma (tclose m) v.
  Proof.
    exact tclose_models.
  Qed.
  Lemma tclose_bot : forall m, tclose m = Unreached -> forall v, ~ models m v.
  Proof.
    intros m Hbot v Hmodel. pose proof (tclose_models m v Hmodel) as Hclosed.
    rewrite Hbot in Hclosed. exact Hclosed.
  Qed.
  Lemma incr_close_sound : forall i j d m v,
    models m v -> (vl v j - vl v i <= d)%Z -> ngamma (incr_close i j d m) v.
  Proof.
    exact incr_close_models.
  Qed.
  (** State size charges all stored numeric data. *)
  Lemma F_size : forall s, size s = (ns s + 1)^2 * (bs s + ells s + 1) + skels s.
  Proof.
    reflexivity.
  Qed.
  (** Range work charges the numeric query and its linearization. *)
  Lemma F_range_work : forall e s, (N.of_nat (range_work e s) =
    N.of_nat ((tsize e + 1) *
      (bs s + ells s + F.bits_e e + Nat.log2 (tsize e) + 1)^2) + F.T_lin_of e)%N.
  Proof.
    intros e s. unfold range_work. rewrite Nat2N.inj_add, N2Nat.id. reflexivity.
  Qed.
  Lemma F_range_bits : forall e s,
    range_bits e s = ells s + F.bits_e e + Nat.log2 (tsize e) + 2.
  Proof.
    reflexivity.
  Qed.
  Fixpoint fw_trace (ks : list K.t) (m : dbm) : list (K.t * dbm) :=
    match ks with
    | nil => nil
    | k :: ks =>
      let m' := fw_round k m in
      (k, m) ::
        match entry m' k k with
        | Some d => if (d <? 0)%Z then nil else fw_trace ks m'
        | None => fw_trace ks m'
        end
    end.
  TimeFun fw_trace.
  (** A round keeps the support and its key bits. *)
  (** Reflected key equality supplies the Boolean test used by deduplication. *)
  Lemma key_eqb_true : forall x y, K.eqb x y = true <-> x = y.
  Proof.
    intros x y. destruct (K.eqb_spec x y); split; congruence.
  Qed.


  (** Pivot collection keeps each key once. *)
  Lemma keys_nodup : forall m, NoDup (keys m).
  Proof.
    intro m. unfold keys. apply (dedup_nodup K.t K.eqb key_eqb_true).
    constructor.
  Qed.


  (** Each consistent pivot label names a code in the matrix support. *)
  Lemma keys_support : forall m k, dbm_wf m -> In k (keys m) ->
    In (K.encode k) (support m).
  Proof.
    intros m k [Houter Hrows] Hkey. unfold keys in Hkey.
    rewrite (dedup_membership K.t K.eqb key_eqb_true) in Hkey.
    destruct Hkey as [Hkey | Hempty]; [|contradiction].
    apply in_app_iff in Hkey. apply support_spec. destruct Hkey as [Hkey | Hkey].
    - left. now apply elements_code.
    - right. apply in_flat_map in Hkey.
      destruct Hkey as [[i row] [Hrow Hkey]]. cbn in Hkey.
      pose proof (proj1 (M.elements_spec (M.t Z) m i row Houter) Hrow) as Hget.
      rewrite M.get_find in Hget.
      apply in_flat_map. exists row. split.
      + exact (row_in_rows m (K.encode i) row Hget).
      + apply elements_code; [exact (Hrows (K.encode i) row Hget)|exact Hkey].
  Qed.
  Lemma bits_fw_round_step : forall k m, ell (fw_round k m) <= ell m + 1.
  Proof.
    intros k m. unfold fw_round.
    change (ell (relax_round k
      (if pivot_present k m then put k k (lower_bound 0%Z (entry m k k)) m else m)) <=
      ell m + 1).
    destruct (pivot_present k m).
    - eapply Nat.le_trans; [apply ell_relax|].
      assert (Hseed : ell (put k k (lower_bound 0%Z (entry m k k)) m) <= ell m).
      { apply ell_put; [lia|]. apply lower_bound_ell; [lia|cbn [Z.size_nat]; lia]. }
      lia.
    - apply ell_relax.
  Qed.
  Lemma path_key_dec : forall x y : K.t, {x = y} + {x <> y}.
  Proof.
    intros x y. destruct (K.eqb_spec x y); [now left|now right].
  Defined.

  (** The executable seed is the abstract zero-diagonal insertion. *)
  Lemma entry_path_seed : forall k m i j,
    entry (put k k (lower_bound 0%Z (entry m k k)) m) i j =
      RelationalPathBounds.seed path_key_dec (entry m) k i j.
  Proof.
    intros k m i j. rewrite entry_put. unfold RelationalPathBounds.seed.
    destruct (K.eqb_spec i k) as [Hi|Hi];
      destruct (path_key_dec i k) as [Hi'|Hi']; try contradiction.
    - subst i. destruct (K.eqb_spec j k) as [Hj|Hj];
        destruct (path_key_dec j k) as [Hj'|Hj']; try contradiction.
      + subst j. destruct (entry m k k); reflexivity.
      + reflexivity.
    - reflexivity.
  Qed.

  Lemma entry_relax_round : forall k m i j,
    entry (relax_round k m) i j =
      match entry m i k with
      | Some a => via_bound a (entry m i j) (entry m k j)
      | None => entry m i j
      end.
  Proof.
    intros k m i j. rewrite <- !raw_entry_get, raw_entry_relax. reflexivity.
  Qed.

  (** Sparse merging agrees pointwise with the abstract Floyd step. *)
  Lemma entry_path_floyd : forall k m i j,
    entry (relax_round k m) i j = RelationalPathBounds.floyd (entry m) k i j.
  Proof.
    intros k m i j. rewrite entry_relax_round. unfold RelationalPathBounds.floyd.
    destruct (entry m i k), (entry m i j), (entry m k j);
      cbn [via_bound lower_bound RelationalPathBounds.minimum RelationalPathBounds.plus];
      try reflexivity. f_equal. apply Z.min_comm.
  Qed.

  Lemma entry_fw_present : forall k m, pivot_present k m = true -> forall i j,
    entry (fw_round k m) i j =
      RelationalPathBounds.floyd
        (RelationalPathBounds.seed path_key_dec (entry m) k) k i j.
  Proof.
    intros k m Hpresent i j. unfold fw_round. rewrite Hpresent.
    change (entry (relax_round k (put k k (lower_bound 0%Z (entry m k k)) m)) i j =
      RelationalPathBounds.floyd
        (RelationalPathBounds.seed path_key_dec (entry m) k) k i j).
    rewrite entry_path_floyd.
    unfold RelationalPathBounds.floyd. now rewrite !entry_path_seed.
  Qed.

  (** Both endpoints of a finite entry are in the raw code support. *)
  Lemma entry_source_support : forall m i j d, entry m i j = Some d ->
    In (K.encode i) (support m).
  Proof.
    intros m i j d Hentry. unfold entry in Hentry.
    destruct (M.get i m) as [row|] eqn:Hrow; [|discriminate].
    apply support_find. left. rewrite <- (M.get_find (M.t Z) i m), Hrow. discriminate.
  Qed.

  Lemma entry_target_support : forall m i j d, entry m i j = Some d ->
    In (K.encode j) (support m).
  Proof.
    intros m i j d Hentry. apply support_find. right. exists (K.encode i).
    rewrite raw_entry_get, Hentry. discriminate.
  Qed.

  Lemma entry_fw_absent : forall k m, pivot_present k m = false -> forall i j,
    entry (fw_round k m) i j = entry m i j.
  Proof.
    intros k m Habsent i j.
    assert (Hcolumn : entry m i k = None).
    { destruct (entry m i k) as [d|] eqn:Hentry; [|reflexivity].
      pose proof (entry_target_support m i k d Hentry) as Hsupport.
      apply pivot_present_support in Hsupport. congruence. }
    unfold fw_round. rewrite Habsent.
    change (entry (relax_round k m) i j = entry m i j).
    now rewrite entry_relax_round, Hcolumn.
  Qed.

  (** A successful actual round extends the processed-path invariant. *)
  Lemma fw_round_path_invariant : forall initial m ps k,
    RelationalPathBounds.invariant (entry initial) (entry m) ps ->
    (forall d, entry (fw_round k m) k k = Some d -> (0 <= d)%Z) ->
    exists ps', RelationalPathBounds.invariant (entry initial) (entry (fw_round k m)) ps'.
  Proof.
    intros initial m ps k Hinv Hnonnegative.
    destruct (pivot_present k m) eqn:Hpresent.
    - exists (k :: ps). eapply RelationalPathBounds.invariant_ext.
      + intros i j. symmetry. now apply entry_fw_present.
      + apply RelationalPathBounds.invariant_successful_round; [exact Hinv|].
        intros d Hdiag. apply Hnonnegative. now rewrite (entry_fw_present k m Hpresent).
    - exists ps. eapply RelationalPathBounds.invariant_ext; [|exact Hinv].
      intros i j. symmetry. now apply entry_fw_absent.
  Qed.

  (** A successful scan processes every supported pivot in the loop. *)
  Lemma fw_pivots_success_path_invariant : forall ks initial m ps,
    RelationalPathBounds.invariant (entry initial) (entry m) ps ->
    (forall k, In k ks -> In (K.encode k) (support m)) ->
    (forall k, In k ks -> nonnegative k (fw_pivots ks m) = true) ->
    RelationalPathBounds.invariant (entry initial) (entry (fw_pivots ks m))
      (rev ks ++ ps).
  Proof.
    induction ks as [|k ks IH]; intros initial m ps Hinv Hsupport Hscan.
    - exact Hinv.
    - cbn [fw_pivots].
      assert (Hpresent : pivot_present k m = true).
      { apply pivot_present_support, Hsupport. now left. }
      destruct (nonnegative k (fw_round k m)) eqn:Hnext.
      + assert (Hsuccess : forall d, entry (fw_round k m) k k = Some d -> (0 <= d)%Z).
        { intros d Hd. unfold nonnegative in Hnext. rewrite Hd in Hnext.
          now apply Z.leb_le. }
        assert (Hround : RelationalPathBounds.invariant (entry initial)
          (entry (fw_round k m)) (k :: ps)).
        { eapply RelationalPathBounds.invariant_ext.
          - intros i j. symmetry. now apply entry_fw_present.
          - eapply RelationalPathBounds.invariant_successful_round;
              [exact Hinv|].
            intros d Hd. apply Hsuccess.
            now rewrite (entry_fw_present k m Hpresent k k). }
        replace (rev (k :: ks) ++ ps) with (rev ks ++ k :: ps)
          by (cbn [rev]; rewrite <- app_assoc; reflexivity).
        apply IH; [exact Hround| |].
        * intros p Hp. rewrite support_round.
          apply Hsupport. now right.
        * intros p Hp. specialize (Hscan p (or_intror Hp)).
          cbn [fw_pivots] in Hscan. now rewrite Hnext in Hscan.
      + specialize (Hscan k (or_introl eq_refl)).
        cbn [fw_pivots] in Hscan. rewrite Hnext in Hscan.
        congruence.
  Qed.

  (** Every recorded state precedes the first rejected pivot cycle. *)
  Lemma fw_trace_path_invariant : forall ks initial m ps k a,
    dbm_wf m -> RelationalPathBounds.invariant (entry initial) (entry m) ps ->
    In (k, a) (fw_trace ks m) -> dbm_wf a /\
      exists ps', RelationalPathBounds.invariant (entry initial) (entry a) ps'.
  Proof.
    induction ks as [|p ks IH]; intros initial m ps k a Hwf Hinv Hin.
    - contradiction.
    - cbn [fw_trace] in Hin. destruct Hin as [Heq|Hin].
      + inversion Heq; subst k a. split; [exact Hwf|now exists ps].
      + assert (Hnext_wf : dbm_wf (fw_round p m)) by (now apply wf_fw_round).
        destruct (entry (fw_round p m) p p) as [d|] eqn:Hdiag.
        * destruct (d <? 0)%Z eqn:Hnegative; [contradiction|].
          apply Z.ltb_ge in Hnegative.
          assert (Hsuccess : forall z, entry (fw_round p m) p p = Some z -> (0 <= z)%Z).
          { intros z Hz. rewrite Hdiag in Hz. inversion Hz. lia. }
          destruct (fw_round_path_invariant initial m ps p Hinv Hsuccess) as [ps' Hnext].
          exact (IH initial (fw_round p m) ps' k a Hnext_wf Hnext Hin).
        * assert (Hsuccess : forall z, entry (fw_round p m) p p = Some z -> (0 <= z)%Z).
          { intros z Hz. rewrite Hdiag in Hz. discriminate. }
          destruct (fw_round_path_invariant initial m ps p Hinv Hsuccess) as [ps' Hnext].
          exact (IH initial (fw_round p m) ps' k a Hnext_wf Hnext Hin).
  Qed.

  (** A minimum path has no more original edges than the initial support has codes. *)
  Lemma path_invariant_entry_bits : forall initial current ps,
    RelationalPathBounds.invariant (entry initial) current ps ->
    forall i j d, current i j = Some d ->
      Z.size_nat d <= ell initial + Nat.log2 (supp initial) + 1.
  Proof.
    intros initial current ps [Hbelow Hclosed Hzero Hpath] i j d Hentry.
    destruct (Hpath i j d Hentry) as [[Heq Hz]|[ks [Hks Hchain]]].
    - subst d. cbn [Z.size_nat]. lia.
    - destruct (RelationalPathBounds.simple_minimum_chain K.t path_key_dec
        (entry initial) current ps Hbelow Hclosed Hzero ks i j d Hks Hentry Hchain)
        as [shortened [Hincl [Hnodup Hvalue]]].
      assert (Hlength : length (i :: shortened) <= supp initial).
      { unfold supp. rewrite <- (length_map K.encode (i :: shortened)).
        apply NoDup_incl_length; [now apply encoded_keys_nodup|].
        intros code Hcode. apply in_map_iff in Hcode.
        destruct Hcode as [x [Hcode Hx]]. subst code.
        eapply (RelationalPathBounds.chain_sources K.t (entry initial)
          (fun q => In (K.encode q) (support initial))).
        - intros p q z Hz. now apply (entry_source_support initial p q z).
        - exact Hvalue.
        - exact Hx. }
      assert (Hedge : forall p q z, entry initial p q = Some z ->
        Z.abs_nat z <= 2 ^ ell initial).
      { intros p q z Hz. apply Nat.lt_le_incl. apply zbits_abs_bound.
        apply (ell_entry initial (K.encode p) (K.encode q) z).
        now rewrite raw_entry_get. }
      pose proof (RelationalPathBounds.chain_abs K.t (entry initial)
        (2 ^ ell initial) Hedge shortened i j d Hvalue) as Habs.
      assert (Hpositive : 0 < supp initial) by (cbn [length] in Hlength; lia).
      pose proof (Nat.log2_spec (supp initial) Hpositive) as [_ Hlog].
      assert (Hpower : 0 < 2 ^ ell initial).
      { pose proof (Nat.pow_nonzero 2 (ell initial) ltac:(lia)). lia. }
      apply zbits_least.
      replace (ell initial + Nat.log2 (supp initial) + 1) with
        (S (Nat.log2 (supp initial)) + ell initial) by lia.
      rewrite Nat.pow_add_r. cbn [length] in Hlength.
      eapply Nat.le_lt_trans; [exact Habs|].
      apply Nat.mul_lt_mono_pos_r; [exact Hpower|lia].
  Qed.

  (** A minimum path uses at most one fewer than a power of two per original edge. *)
  Lemma path_invariant_entry_abs : forall initial current ps,
    RelationalPathBounds.invariant (entry initial) current ps ->
    forall i j d, current i j = Some d ->
      Z.abs_nat d <= supp initial * (2 ^ ell initial - 1).
  Proof.
    intros initial current ps [Hbelow Hclosed Hzero Hpath] i j d Hentry.
    destruct (Hpath i j d Hentry) as [[Heq Hz]|[ks [Hks Hchain]]].
    - subst d. cbn [Z.abs_nat]. nia.
    - destruct (RelationalPathBounds.simple_minimum_chain K.t path_key_dec
        (entry initial) current ps Hbelow Hclosed Hzero ks i j d Hks Hentry Hchain)
        as [shortened [Hincl [Hnodup Hvalue]]].
      assert (Hlength : length (i :: shortened) <= supp initial).
      { unfold supp. rewrite <- (length_map K.encode (i :: shortened)).
        apply NoDup_incl_length; [now apply encoded_keys_nodup|].
        intros code Hcode. apply in_map_iff in Hcode.
        destruct Hcode as [x [Hcode Hx]]. subst code.
        eapply (RelationalPathBounds.chain_sources K.t (entry initial)
          (fun q => In (K.encode q) (support initial))).
        - intros p q z Hz. now apply (entry_source_support initial p q z).
        - exact Hvalue.
        - exact Hx. }
      assert (Hedge : forall p q z, entry initial p q = Some z ->
        Z.abs_nat z <= 2 ^ ell initial - 1).
      { intros p q z Hz. pose proof (zbits_abs_bound z (ell initial)) as Hbits.
        specialize (Hbits (ell_entry initial (K.encode p) (K.encode q) z
          ltac:(now rewrite raw_entry_get))). lia. }
      pose proof (RelationalPathBounds.chain_abs K.t (entry initial)
        (2 ^ ell initial - 1) Hedge shortened i j d Hvalue) as Habs.
      cbn [length] in Hlength. nia.
  Qed.

  (** Well-formed raw entries have source and target keys. *)
  Lemma wf_raw_entry_keys : forall m p q d, dbm_wf m -> raw_entry m p q = Some d ->
    exists i j, K.encode i = p /\ K.encode j = q /\ entry m i j = Some d.
  Proof.
    intros m p q d [Houter Hrows] Hraw.
    unfold raw_entry in Hraw. destruct (M.find p m) as [row|] eqn:Hrow;
      cbn [row_of] in Hraw.
    - destruct (M.wf_find (M.t Z) m p row Houter Hrow) as [i Hi].
      destruct (M.wf_find Z row q d (Hrows p row Hrow) Hraw) as [j Hj].
      exists i, j. split; [exact Hi|]. split; [exact Hj|].
      rewrite <- raw_entry_get, Hi, Hj. unfold raw_entry. now rewrite Hrow.
    - rewrite M.find_empty in Hraw. discriminate.
  Qed.

  Lemma bits_fw_trace_le : forall ks m k a, dbm_wf m ->
    In (k, a) (fw_trace ks m) ->
    ell a <= ell m + Nat.log2 (supp m) + 1.
  Proof.
    intros ks m k a Hwf Hin.
    destruct (fw_trace_path_invariant ks m m nil k a Hwf
      (RelationalPathBounds.invariant_initial K.t (entry m)) Hin) as [Hawf [ps Hpath]].
    apply ell_bound. intros p q d Hraw.
    destruct (wf_raw_entry_keys a p q d Hawf Hraw) as [i [j [Hi [Hj Hentry]]]].
    exact (path_invariant_entry_bits m (entry a) ps Hpath i j d Hentry).
  Qed.
  Lemma supp_fw_round : forall k m,
    supp (fw_round k m) = supp m /\ b (fw_round k m) = b m.
  Proof.
    intros k m. apply support_sizes, support_round.
  Qed.
  (** A consistent matrix has no more pivot keys than codes in its support. *)
  Lemma keys_le : forall m, dbm_wf m -> length (keys m) <= supp m.
  Proof.
    intros m Hwf. unfold supp.
    rewrite <- (length_map K.encode (keys m)). apply NoDup_incl_length.
    - apply encoded_keys_nodup, keys_nodup.
    - intros p Hin. apply in_map_iff in Hin. destruct Hin as [k [Hcode Hkey]].
      subst p. now apply keys_support.
  Qed.

  (** The Boolean list scan recognizes key membership through the key equality law. *)
  Lemma key_existsb : forall k ks, existsb (K.eqb k) ks = true <-> In k ks.
  Proof.
    intros k ks. rewrite existsb_exists. split.
    - intros [x [Hx Heq]]. apply key_eqb_true in Heq. now subst x.
    - intro Hk. exists k. split; [exact Hk|apply key_eqb_true; reflexivity].
  Qed.

  Definition keyset_matches (seen : M.t unit) (ks : list K.t) : Prop :=
    forall k, M.get k seen <> None <-> In k ks.

  (** Inserting a remembered key preserves the membership correspondence. *)
  Lemma keyset_add_matches : forall seen ks k,
    keyset_matches seen ks -> keyset_matches (M.set k tt seen) (k :: ks).
  Proof.
    intros seen ks k Hmatch q. destruct (K.eqb_spec q k) as [Heq|Hne].
    - subst q. rewrite M.get_set_same. cbn [In]. split.
      + intros. now left.
      + intros. discriminate.
    - rewrite M.get_set_other by exact Hne. rewrite (Hmatch q). cbn [In].
      split; [intro Hin; now right|]. intros [Heq|Hin]; [|exact Hin].
      exfalso. apply Hne. now symmetry.
  Qed.

  (** The map-backed fold preserves the signature's reverse first-occurrence order. *)
  Lemma remember_fold_keys : forall xs seen ks,
    keyset_matches seen ks ->
    snd (fold_left remember_key xs (seen, ks)) =
    fold_left (fun acc x => if existsb (K.eqb x) acc then acc else x :: acc) xs ks.
  Proof.
    intro xs. induction xs as [|k xs IH]; intros seen ks Hmatch; [reflexivity|].
    cbn [fold_left]. destruct (M.get k seen) as [u|] eqn:Hget.
    - assert (Hremember : remember_key (seen, ks) k = (seen, ks)).
      { unfold remember_key. cbn [fst snd]. now rewrite Hget. }
      assert (Hseen : existsb (K.eqb k) ks = true).
      { apply key_existsb, (proj1 (Hmatch k)). rewrite Hget. discriminate. }
      rewrite Hremember, Hseen. now apply IH.
    - assert (Hremember : remember_key (seen, ks) k = (M.set k tt seen, k :: ks)).
      { unfold remember_key. cbn [fst snd]. now rewrite Hget. }
      assert (Hseen : existsb (K.eqb k) ks = false).
      { destruct (existsb (K.eqb k) ks) eqn:Hseen; [|reflexivity].
        apply key_existsb in Hseen. apply (proj2 (Hmatch k)) in Hseen.
        contradiction. }
      rewrite Hremember, Hseen. apply IH. now apply keyset_add_matches.
  Qed.

  (** Executable pivot enumeration agrees with the frozen specification even on raw maps. *)
  Lemma pivot_keys_eq_keys : forall m, pivot_keys m = keys m.
  Proof.
    intro m. unfold pivot_keys, keys. apply remember_fold_keys.
    intro k. rewrite M.get_empty. cbn [In]. tauto.
  Qed.

  (** The executable loop returns precisely the result of its recorded rounds. *)
  Lemma fw_pivots_trace : forall ks m,
    fw_pivots ks m =
    fold_left (fun a km => fw_round (fst km) a) (fw_trace ks m) m.
  Proof.
    intro ks. induction ks as [|k ks IH]; intro m; [reflexivity|].
    cbn [fw_pivots fw_trace fold_left fst]. unfold nonnegative.
    destruct (entry (fw_round k m) k k) as [d|] eqn:Hdiag; [|apply IH].
    destruct (d <? 0)%Z eqn:Hneg.
    - apply Z.ltb_lt in Hneg.
      assert (Htest : (0 <=? d)%Z = false) by (apply Z.leb_gt; lia).
      rewrite Htest. reflexivity.
    - apply Z.ltb_ge in Hneg.
      assert (Htest : (0 <=? d)%Z = true) by (apply Z.leb_le; lia).
      rewrite Htest. apply IH.
  Qed.
  (** Floyd-Warshall runs the traced rounds over the pivot keys. *)
  Lemma F_fw : forall m, fw m =
    fold_left (fun a km => fw_round (fst km) a) (fw_trace (keys m) m) m.
  Proof.
    intro m. unfold fw. rewrite pivot_keys_eq_keys. apply fw_pivots_trace.
  Qed.
  Definition diag_ok (m : dbm) : bool :=
    forallb (fun k => match entry m k k with Some d => (0 <=? d)%Z | None => true end) (keys m).
  TimeFun diag_ok.
  (** Tight closure tightens and strengthens only a consistent closed matrix. *)
  (** A replacement row has the same finite coordinates as its validated source row. *)
  Definition tightened_rows (m changed : dbm) : Prop :=
    forall p row, M.find p changed = Some row ->
      forall q, M.find q row <> None <-> raw_entry m p q <> None.

  Lemma tighten_row_presence : forall m changed k ignored,
    tightened_rows m changed -> tightened_rows m (tighten_row m changed k ignored).
  Proof.
    intros m changed k ignored Hchanged. unfold tighten_row.
    destruct (M.get k changed); [exact Hchanged|].
    destruct (M.get k m) as [row|] eqn:Hrow; [|exact Hchanged].
    destruct (M.get (flip k) row) as [d|] eqn:Hbound; [|exact Hchanged].
    intros p fresh Hfresh q. rewrite M.find_set in Hfresh.
    destruct (Pos.eqb p (K.encode k)) eqn:Hkey.
    - apply Pos.eqb_eq in Hkey. subst p. injection Hfresh as <-.
      unfold raw_entry. rewrite <- (M.get_find (M.t Z) k m), Hrow. cbn [row_of].
      rewrite M.find_set. destruct (Pos.eqb q (K.encode (flip k))) eqn:Hcolumn.
      + apply Pos.eqb_eq in Hcolumn. subst q. rewrite <- M.get_find, Hbound.
        split; discriminate.
      + reflexivity.
    - now apply (Hchanged p fresh Hfresh q).
  Qed.

  Lemma collected_tighten_presence : forall m,
    tightened_rows m (M.fold (tighten_row m) m M.empty).
  Proof.
    intro m. apply (fold_invariant _ _ (tightened_rows m)).
    - intros p row Hrow. rewrite M.find_empty in Hrow. discriminate.
    - intros changed k ignored Hchanged. now apply tighten_row_presence.
  Qed.

  Lemma find_tighten_presence : forall m p,
    M.find p (tighten m) <> None <-> M.find p m <> None.
  Proof.
    intros m p. unfold tighten. rewrite M.find_merge by reflexivity.
    destruct (M.find p m), (M.find p (M.fold (tighten_row m) m M.empty));
      cbn [replace_row]; split; congruence.
  Qed.

  Lemma raw_tighten_presence : forall m p q,
    raw_entry (tighten m) p q <> None <-> raw_entry m p q <> None.
  Proof.
    intros m p q. unfold raw_entry at 1, tighten.
    rewrite M.find_merge by reflexivity.
    destruct (M.find p m) as [row|] eqn:Hrow; cbn [replace_row row_of].
    - destruct (M.find p (M.fold (tighten_row m) m M.empty)) as [fresh|] eqn:Hfresh;
        cbn [row_of].
      + now apply (collected_tighten_presence m p fresh Hfresh q).
      + unfold raw_entry. now rewrite Hrow.
    - unfold raw_entry. now rewrite Hrow.
  Qed.

  Lemma support_tighten : forall m p,
    In p (support (tighten m)) <-> In p (support m).
  Proof.
    intros m p. rewrite !support_find, find_tighten_presence.
    split; intros [Hrow|[q Hentry]].
    - now left.
    - right. exists q. exact (proj1 (raw_tighten_presence m q p) Hentry).
    - now left.
    - right. exists q. exact (proj2 (raw_tighten_presence m q p) Hentry).
  Qed.

  Lemma find_strengthen_presence : forall m p,
    M.find p (strengthen m) <> None <-> M.find p m <> None.
  Proof.
    intros m p. unfold strengthen. rewrite M.find_merge by reflexivity.
    destruct (M.find p m); cbn [strengthen_outer]; split; congruence.
  Qed.

  (** Strengthening introduces only pairs supplied by the two validated unary maps. *)
  Lemma raw_strengthen_presence : forall m p q,
    raw_entry (strengthen m) p q <> None <->
    raw_entry m p q <> None \/
    (M.find p m <> None /\
      M.find p (fst (M.fold (unary_maps m) m (M.empty, M.empty))) <> None /\
      M.find q (snd (M.fold (unary_maps m) m (M.empty, M.empty))) <> None).
  Proof.
    intros m p q. unfold raw_entry, strengthen.
    rewrite M.find_merge by reflexivity.
    destruct (M.find p m) as [row|]; cbn [strengthen_outer row_of].
    - destruct (M.find p (fst (M.fold (unary_maps m) m (M.empty, M.empty)))).
      + rewrite M.find_merge by reflexivity.
        destruct (M.find q row),
          (M.find q (snd (M.fold (unary_maps m) m (M.empty, M.empty))));
          cbn [strengthen_bound]; intuition congruence.
      + intuition congruence.
    - rewrite M.find_empty. intuition congruence.
  Qed.

  Lemma support_strengthen : forall m p,
    In p (support (strengthen m)) <-> In p (support m).
  Proof.
    intros m p. rewrite !support_find, find_strengthen_presence.
    split; intros [Hrow|[q Hentry]].
    - now left.
    - apply raw_strengthen_presence in Hentry.
      destruct Hentry as [Hentry|[Hrow [Hleft Hright]]].
      + right. now exists q.
      + pose proof (collect_unary_origins m) as [_ Horigins].
        destruct (M.find p (snd (M.fold (unary_maps m) m (M.empty, M.empty))))
          as [d|] eqn:Hfound; [|contradiction].
        destruct (Horigins p d Hfound) as [k [Hcode Hsource]].
        right. exists (K.encode k). subst p.
        rewrite raw_entry_get, Hsource. discriminate.
    - now left.
    - right. exists q. apply raw_strengthen_presence. now left.
  Qed.


  (** Tightening and strengthening keep the support. *)
  Lemma supp_tighten_strengthen : forall m,
    supp (tighten m) = supp m /\ b (tighten m) = b m /\
    supp (strengthen m) = supp m /\ b (strengthen m) = b m.
  Proof.
    intro m. pose proof (support_sizes (tighten m) m (support_tighten m)) as [Hst Hbt].
    pose proof (support_sizes (strengthen m) m (support_strengthen m)) as [Hss Hbs].
    repeat split; assumption.
  Qed.
  (** The incremental merge is named here only to state raw-coordinate invariants. *)
  Local Definition increment_matrix (i j : K.t) (d : Z) (m : dbm) : dbm :=
    M.merge
      (increment_row i j d (row_of (M.get j m)) (row_of (M.get (flip i) m))
        (entry m j (flip j)) (entry m (flip i) i)) m M.empty.

  Local Definition relax_value (prefix old exit : option Z) : option Z :=
    match prefix with Some a => via_bound a old exit | None => old end.

  Lemma find_relax_row : forall prefix row exit q,
    M.find q (relax_row prefix row exit) =
    relax_value prefix (M.find q row) (M.find q exit).
  Proof.
    intros [a|] row exit q; [|reflexivity].
    unfold relax_row, relax_value. now rewrite M.find_merge by reflexivity.
  Qed.

  (** Every incremental candidate uses only prefix and suffix data from the same seed. *)
  Lemma raw_entry_increment : forall i j d m p q,
    raw_entry (increment_matrix i j d m) p q =
    relax_value (twin_prefix d (raw_entry m p (K.encode (flip j))) (entry m (flip i) i))
      (relax_value (twin_prefix d (raw_entry m p (K.encode i)) (entry m j (flip j)))
        (relax_value (edge_prefix d (raw_entry m p (K.encode (flip j))))
          (relax_value (edge_prefix d (raw_entry m p (K.encode i)))
            (raw_entry m p q) (raw_entry m (K.encode j) q))
          (raw_entry m (K.encode (flip i)) q))
        (raw_entry m (K.encode (flip i)) q))
      (raw_entry m (K.encode j) q).
  Proof.
    intros i j d m p q. unfold increment_matrix, raw_entry at 1.
    rewrite M.find_merge by reflexivity. rewrite M.find_empty.
    destruct (M.find p m) as [row|] eqn:Hrow; cbn [increment_row row_of].
    - rewrite !find_relax_row. unfold raw_entry. rewrite Hrow.
      cbn [row_of]. now rewrite !M.get_find.
    - unfold raw_entry. rewrite Hrow. cbn [row_of].
      rewrite !M.find_empty. reflexivity.
  Qed.

  Lemma relax_value_presence : forall prefix old exit,
    relax_value prefix old exit <> None <->
    old <> None \/ (prefix <> None /\ exit <> None).
  Proof.
    intros [a|] [z|] [b|]; cbn [relax_value via_bound]; intuition congruence.
  Qed.

  Lemma find_increment_presence : forall i j d m p,
    M.find p (increment_matrix i j d m) <> None <-> M.find p m <> None.
  Proof.
    intros i j d m p. unfold increment_matrix.
    rewrite M.find_merge by reflexivity. rewrite M.find_empty.
    destruct (M.find p m); cbn [increment_row]; split; congruence.
  Qed.

  Lemma raw_increment_columns : forall i j d m p q,
    raw_entry (increment_matrix i j d m) p q <> None ->
    raw_entry m p q <> None \/
    raw_entry m (K.encode j) q <> None \/ raw_entry m (K.encode (flip i)) q <> None.
  Proof.
    intros i j d m p q. rewrite raw_entry_increment, !relax_value_presence. tauto.
  Qed.

  Lemma raw_increment_retains : forall i j d m p q,
    raw_entry m p q <> None -> raw_entry (increment_matrix i j d m) p q <> None.
  Proof.
    intros i j d m p q. rewrite raw_entry_increment, !relax_value_presence. tauto.
  Qed.

  (** The four candidate paths preserve the seed's raw support exactly. *)
  Lemma support_increment : forall i j d m p,
    In p (support (increment_matrix i j d m)) <-> In p (support m).
  Proof.
    intros i j d m p. rewrite !support_find. split.
    - intros [Hrow|[q Hentry]].
      + left. now apply find_increment_presence in Hrow.
      + apply raw_increment_columns in Hentry. right.
        destruct Hentry as [Hentry|[Hentry|Hentry]].
        * now exists q.
        * now exists (K.encode j).
        * now exists (K.encode (flip i)).
    - intros [Hrow|[q Hentry]].
      + left. now apply find_increment_presence.
      + right. exists q. now apply raw_increment_retains.
  Qed.

  (** Inserting both signed twins adds only the four signed endpoint codes. *)
  Lemma support_add_cons : forall i j d m p,
    In p (support (add_cons i j d m)) <->
    p = K.encode i \/ p = K.encode j \/ p = K.encode (flip i) \/
      p = K.encode (flip j) \/ In p (support m).
  Proof.
    intros i j d m p. unfold add_cons. rewrite !support_put. tauto.
  Qed.

  Lemma support_signed_endpoints : forall i j ma mb,
    (forall p, In p (support ma) ->
      p = K.encode i \/ p = K.encode j \/ p = K.encode (flip i) \/
        p = K.encode (flip j) \/ In p (support mb)) ->
    supp ma <= supp mb + 4 /\
    b ma <= Nat.max (b mb) (Nat.max (K.bits i) (K.bits j) + 1).
  Proof.
    intros i j ma mb Hsupport. split.
    - assert (Hincl : incl (support ma)
        (K.encode i :: K.encode j :: K.encode (flip i) :: K.encode (flip j) :: support mb)).
      { intros p Hin. destruct (Hsupport p Hin) as [Heq|[Heq|[Heq|[Heq|Hin']]]];
          cbn; intuition congruence. }
      pose proof (NoDup_incl_length (support_nodup ma) Hincl) as Hlength.
      unfold supp. cbn in Hlength. lia.
    - unfold b at 1. apply maximum_bound. intros p Hin.
      pose proof (Nat.le_max_l (K.bits i) (K.bits j)) as Hi.
      pose proof (Nat.le_max_r (K.bits i) (K.bits j)) as Hj.
      pose proof (Nat.le_max_r (b mb) (Nat.max (K.bits i) (K.bits j) + 1)) as Hright.
      destruct (Hsupport p Hin) as [Heq|[Heq|[Heq|[Heq|Hin']]]].
      + subst p.
        change (K.bits i <= Nat.max (b mb) (Nat.max (K.bits i) (K.bits j) + 1)). lia.
      + subst p.
        change (K.bits j <= Nat.max (b mb) (Nat.max (K.bits i) (K.bits j) + 1)). lia.
      + subst p.
        change (K.bits (flip i) <= Nat.max (b mb) (Nat.max (K.bits i) (K.bits j) + 1)).
        pose proof (flip_bits i). lia.
      + subst p.
        change (K.bits (flip j) <= Nat.max (b mb) (Nat.max (K.bits i) (K.bits j) + 1)).
        pose proof (flip_bits j). lia.
      + eapply Nat.le_trans; [exact (support_bits mb p Hin')|apply Nat.le_max_l].
  Qed.

  Local Definition bound_bits (upper : nat) (bound : option Z) : Prop :=
    forall z, bound = Some z -> Z.size_nat z <= upper.

  Lemma edge_prefix_bits : forall d a upper,
    Z.size_nat d <= upper -> bound_bits upper a ->
    bound_bits (upper + 2) (edge_prefix d a).
  Proof.
    intros d [a|] upper Hd Ha z Hentry; cbn [edge_prefix] in Hentry; [|discriminate].
    injection Hentry as <-.
    pose proof (zbits_add_bound a d upper (Ha a eq_refl) Hd). lia.
  Qed.

  Lemma twin_prefix_bits : forall d a cross upper,
    Z.size_nat d <= upper -> bound_bits upper a -> bound_bits upper cross ->
    bound_bits (upper + 2) (twin_prefix d a cross).
  Proof.
    intros d [a|] [cross|] upper Hd Ha Hcross z Hentry;
      cbn [twin_prefix] in Hentry; try discriminate.
    injection Hentry as <-.
    replace (a + d + cross + d)%Z with ((a + d) + (cross + d))%Z by ring.
    replace (upper + 2) with ((upper + 1) + 1) by lia.
    apply zbits_add_bound.
    - apply zbits_add_bound; [apply Ha; reflexivity|exact Hd].
    - apply zbits_add_bound; [apply Hcross; reflexivity|exact Hd].
  Qed.

  Lemma relax_value_bits : forall prefix old exit upper,
    bound_bits (upper + 2) prefix -> bound_bits (upper + 3) old ->
    bound_bits upper exit -> bound_bits (upper + 3) (relax_value prefix old exit).
  Proof.
    intros [a|] old [b|] upper Ha Hold Hb z Hentry; cbn [relax_value via_bound] in Hentry.
    - injection Hentry as <-. apply lower_bound_size; [|exact Hold].
      replace (upper + 3) with ((upper + 2) + 1) by lia.
      apply zbits_add_bound; [apply Ha; reflexivity|].
      pose proof (Hb b eq_refl). lia.
    - now apply Hold.
    - now apply Hold.
    - now apply Hold.
  Qed.

  (** Five old or inserted edge weights require at most three additional bits. *)
  Lemma ell_increment : forall i j d m upper,
    ell m <= upper -> Z.size_nat d <= upper ->
    ell (increment_matrix i j d m) <= upper + 3.
  Proof.
    intros i j d m upper Hm Hd.
    assert (Hraw : forall p q, bound_bits upper (raw_entry m p q)).
    { intros p q z Hentry. pose proof (ell_entry m p q z Hentry). lia. }
    assert (Hentry : forall a b, bound_bits upper (entry m a b)).
    { intros a b. rewrite <- raw_entry_get. apply Hraw. }
    apply ell_bound. intros p q.
    change (bound_bits (upper + 3) (raw_entry (increment_matrix i j d m) p q)).
    rewrite raw_entry_increment. apply relax_value_bits.
    - apply twin_prefix_bits; auto.
    - apply relax_value_bits.
      + apply twin_prefix_bits; auto.
      + apply relax_value_bits.
        * apply edge_prefix_bits; auto.
        * apply relax_value_bits.
          -- apply edge_prefix_bits; auto.
          -- intros old Hold. pose proof (Hraw p q old Hold). lia.
          -- apply Hraw.
        * apply Hraw.
      + apply Hraw.
    - apply Hraw.
  Qed.

  Lemma weight_put : forall i j d m,
    M.weight (put i j d m) <= M.weight m + K.bits i + 1.
  Proof.
    intros i j d m. unfold put. apply M.weight_set.
  Qed.

  Lemma weight_add_cons : forall i j d m,
    M.weight (add_cons i j d m) <= M.weight m + K.bits i + K.bits (flip j) + 2.
  Proof.
    intros i j d m. unfold add_cons.
    eapply Nat.le_trans; [apply weight_put|].
    pose proof (weight_put (flip j) (flip i)
      (lower_bound d (entry m (flip j) (flip i))) m). lia.
  Qed.

  Lemma weight_increment : forall i j d m,
    M.weight (increment_matrix i j d m) <= M.weight m.
  Proof.
    intros i j d m. unfold increment_matrix. apply M.weight_merge_l. reflexivity.
  Qed.

  (** Incremental closure grows support only at signed endpoints and bounds each new path. *)
  Lemma grow_incr_close : forall i j d m m', incr_close i j d m = Reached m' ->
    supp m' <= supp m + 4 /\
    b m' <= Nat.max (b m) (Nat.max (K.bits i) (K.bits j) + 1) /\
    ell m' <= Nat.max (ell m) (Z.size_nat d) + 4 /\
    M.weight m' <= M.weight m + 4 * (Nat.max (K.bits i) (K.bits j) + 2).
  Proof.
    intros i j d m m' Hclose. unfold incr_close in Hclose.
    set (seed := add_cons j j 0%Z (add_cons i i 0%Z m)) in *.
    change ((if matrix_ok (increment_matrix i j d seed) then
      if matrix_ok (strengthen (tighten (increment_matrix i j d seed))) then
        Reached (strengthen (tighten (increment_matrix i j d seed))) else Unreached
      else Unreached) = Reached m') in Hclose.
    set (next := increment_matrix i j d seed) in *.
    destruct (matrix_ok next); [|discriminate].
    destruct (matrix_ok (strengthen (tighten next))); [|discriminate].
    injection Hclose as <-.
    assert (Hsupport : forall p, In p (support (strengthen (tighten next))) ->
      p = K.encode i \/ p = K.encode j \/ p = K.encode (flip i) \/
        p = K.encode (flip j) \/ In p (support m)).
    { intros p Hin. apply (proj1 (support_strengthen (tighten next) p)) in Hin.
      apply (proj1 (support_tighten next p)) in Hin.
      unfold next in Hin. apply (proj1 (support_increment i j d seed p)) in Hin.
      unfold seed in Hin. rewrite !support_add_cons in Hin. tauto. }
    destruct (support_signed_endpoints i j (strengthen (tighten next)) m Hsupport)
      as [Hcount Hbits]. split; [exact Hcount|]. split; [exact Hbits|]. split.
    - pose proof (bits_strengthen_le (tighten next)) as Hstrengthen.
      pose proof (bits_tighten_le next) as Htighten.
      assert (Hnext : ell next <= Nat.max (ell m) (Z.size_nat d) + 3).
      { unfold next. apply ell_increment; [|apply Nat.le_max_r].
        unfold seed. apply ell_add_cons; [|cbn [Z.size_nat]; lia].
        apply ell_add_cons; [apply Nat.le_max_l|cbn [Z.size_nat]; lia]. }
      lia.
    - eapply Nat.le_trans; [apply weight_strengthen|].
      eapply Nat.le_trans; [apply weight_tighten|].
      unfold next. eapply Nat.le_trans; [apply weight_increment|].
      unfold seed.
      pose proof (weight_add_cons j j 0%Z (add_cons i i 0%Z m)) as Hj.
      pose proof (weight_add_cons i i 0%Z m) as Hi.
      pose proof (flip_bits i). pose proof (flip_bits j).
      pose proof (Nat.le_max_l (K.bits i) (K.bits j)).
      pose proof (Nat.le_max_r (K.bits i) (K.bits j)). lia.
  Qed.


  (** Key equality commutes with the involution on signed literals. *)
  Lemma key_eqb_flip_left : forall a b,
    K.eqb (flip a) b = K.eqb a (flip b).
  Proof.
    intros a b. destruct (K.eqb_spec (flip a) b) as [Hab|Hab];
      destruct (K.eqb_spec a (flip b)) as [Hba|Hba]; try reflexivity.
    - exfalso. apply Hba. rewrite <- Hab, flip_involutive. reflexivity.
    - exfalso. apply Hab. rewrite Hba, flip_involutive. reflexivity.
  Qed.

  Lemma key_eqb_flip_both : forall a b,
    K.eqb (flip a) (flip b) = K.eqb a b.
  Proof.
    intros a b. rewrite key_eqb_flip_left, flip_involutive. reflexivity.
  Qed.

  Local Definition same_coordinate (a b i j : K.t) : bool :=
    andb (K.eqb a i) (K.eqb b j).

  Lemma entry_put_coordinate : forall i j d m a b,
    entry (put i j d m) a b =
    if same_coordinate a b i j then Some d else entry m a b.
  Proof.
    intros i j d m a b. rewrite entry_put. unfold same_coordinate.
    destruct (K.eqb a i), (K.eqb b j); reflexivity.
  Qed.

  (** Twin insertion changes precisely its two signed coordinates. *)
  Lemma entry_add_cons_coordinates : forall i j d m a b,
    entry (add_cons i j d m) a b =
      if same_coordinate a b i j then Some (lower_bound d (entry m i j))
      else if same_coordinate a b (flip j) (flip i)
        then Some (lower_bound d (entry m (flip j) (flip i)))
        else entry m a b.
  Proof.
    intros i j d m a b. unfold add_cons.
    now rewrite !entry_put_coordinate.
  Qed.

  Lemma same_coordinate_true : forall a b i j,
    same_coordinate a b i j = true -> a = i /\ b = j.
  Proof.
    intros a b i j Hsame. unfold same_coordinate in Hsame.
    apply andb_true_iff in Hsame. destruct Hsame as [Ha Hb].
    apply key_eqb_true in Ha. apply key_eqb_true in Hb. now split.
  Qed.

  Lemma add_cons_entry_below : forall i j d m a b,
    RelationalPathBounds.below (entry (add_cons i j d m) a b) (entry m a b).
  Proof.
    intros i j d m a b. rewrite entry_add_cons_coordinates.
    destruct (same_coordinate a b i j) eqn:Hfirst.
    - destruct (same_coordinate_true a b i j Hfirst) as [Ha Hb].
      subst a b. destruct (entry m i j) as [old|];
        cbn [lower_bound RelationalPathBounds.below];
        [apply Z.le_min_r|exact I].
    - destruct (same_coordinate a b (flip j) (flip i)) eqn:Hsecond.
      + destruct (same_coordinate_true a b (flip j) (flip i) Hsecond)
          as [Ha Hb]. subst a b.
        destruct (entry m (flip j) (flip i)) as [old|];
          cbn [lower_bound RelationalPathBounds.below];
          [apply Z.le_min_r|exact I].
      + apply RelationalPathBounds.below_refl.
  Qed.

  Lemma add_cons_inserted_bounds : forall m i j d,
    RelationalPathBounds.below (entry (add_cons i j d m) i j) (Some d) /\
    RelationalPathBounds.below
      (entry (add_cons i j d m) (flip j) (flip i)) (Some d).
  Proof.
    intros m i j d. split; rewrite entry_add_cons_coordinates.
    - assert (Hsame : same_coordinate i j i j = true).
      { unfold same_coordinate. apply andb_true_iff. split;
          apply key_eqb_true; reflexivity. }
      rewrite Hsame. destruct (entry m i j) as [old|];
        cbn [lower_bound RelationalPathBounds.below]; [apply Z.le_min_l|lia].
    - destruct (same_coordinate (flip j) (flip i) i j) eqn:Hfirst.
      + destruct (entry m i j) as [old|];
          cbn [lower_bound RelationalPathBounds.below]; [apply Z.le_min_l|lia].
      + assert (Hsame : same_coordinate (flip j) (flip i) (flip j) (flip i) = true).
        { unfold same_coordinate. apply andb_true_iff. split;
            apply key_eqb_true; reflexivity. }
        rewrite Hsame. destruct (entry m (flip j) (flip i)) as [old|];
          cbn [lower_bound RelationalPathBounds.below]; [apply Z.le_min_l|lia].
  Qed.

  (** Zero insertion preserves zero or absent diagonal entries. *)
  Lemma add_zero_diagonal_cases : forall m p,
    (forall k, entry m k k = None \/ entry m k k = Some 0%Z) ->
    forall k, entry (add_cons p p 0%Z m) k k = None \/
      entry (add_cons p p 0%Z m) k k = Some 0%Z.
  Proof.
    intros m p Hdiag k. rewrite entry_add_cons_coordinates.
    destruct (same_coordinate k k p p) eqn:Hfirst.
    - right. destruct (Hdiag p) as [Hnone|Hzero];
        rewrite Hnone || rewrite Hzero; reflexivity.
    - destruct (same_coordinate k k (flip p) (flip p)) eqn:Hsecond.
      + right. destruct (Hdiag (flip p)) as [Hnone|Hzero];
          rewrite Hnone || rewrite Hzero; reflexivity.
      + exact (Hdiag k).
  Qed.

  Lemma add_zero_own_diagonal : forall m p,
    (forall k, entry m k k = None \/ entry m k k = Some 0%Z) ->
    entry (add_cons p p 0%Z m) p p = Some 0%Z.
  Proof.
    intros m p Hdiag. rewrite entry_add_cons_coordinates.
    unfold same_coordinate. destruct (K.eqb_spec p p); [|contradiction].
    cbn. destruct (Hdiag p) as [Hnone|Hzero];
      rewrite Hnone || rewrite Hzero; reflexivity.
  Qed.

  Lemma add_zero_flip_diagonal : forall m p,
    (forall k, entry m k k = None \/ entry m k k = Some 0%Z) ->
    entry (add_cons p p 0%Z m) (flip p) (flip p) = Some 0%Z.
  Proof.
    intros m p Hdiag. rewrite entry_add_cons_coordinates.
    unfold same_coordinate.
    destruct (K.eqb_spec (flip p) p) as [Heq|Hne].
    - destruct p as [x sign]. destruct sign; discriminate Heq.
    - destruct (K.eqb_spec (flip p) (flip p)); [|contradiction].
      cbn. destruct (Hdiag (flip p)) as [Hnone|Hzero];
        rewrite Hnone || rewrite Hzero; reflexivity.
  Qed.

  Lemma add_zero_preserve_diagonal : forall m p k,
    (forall q, entry m q q = None \/ entry m q q = Some 0%Z) ->
    entry m k k = Some 0%Z ->
    entry (add_cons p p 0%Z m) k k = Some 0%Z.
  Proof.
    intros m p k Hdiag Hzero. rewrite entry_add_cons_coordinates.
    destruct (same_coordinate k k p p).
    - destruct (Hdiag p) as [Hnone|Hz];
        rewrite Hnone || rewrite Hz; reflexivity.
    - destruct (same_coordinate k k (flip p) (flip p)).
      + destruct (Hdiag (flip p)) as [Hnone|Hz];
          rewrite Hnone || rewrite Hz; reflexivity.
      + exact Hzero.
  Qed.

  Lemma tightly_closed_diagonal_cases : forall m, tightly_closed m ->
    forall k, entry m k k = None \/ entry m k k = Some 0%Z.
  Proof.
    intros m [[Hcoh [Hzero [Htri Hstrong]]] Heven] k.
    destruct (entry m k k) as [d|] eqn:Hentry; [right|now left].
    pose proof (Hzero k (entry_source_support m k k d Hentry)) as Hdiag.
    now rewrite Hentry in Hdiag.
  Qed.

  Lemma incremental_seed_diagonals : forall m i j, tightly_closed m ->
    let seed := add_cons j j 0%Z (add_cons i i 0%Z m) in
    entry seed i i = Some 0%Z /\ entry seed j j = Some 0%Z.
  Proof.
    intros m i j Htight. cbn beta iota zeta.
    set (first := add_cons i i 0%Z m).
    assert (Hdiag : forall k, entry m k k = None \/ entry m k k = Some 0%Z).
    { now apply tightly_closed_diagonal_cases. }
    assert (Hfirst : forall k, entry first k k = None \/
      entry first k k = Some 0%Z).
    { unfold first. now apply add_zero_diagonal_cases. }
    split.
    - apply add_zero_preserve_diagonal; [exact Hfirst|].
      unfold first. now apply add_zero_own_diagonal.
    - now apply add_zero_own_diagonal.
  Qed.

  (** Tight triangle closure holds at every signed key, including absent labels. *)
  Lemma tightly_closed_at_every_key : forall m, tightly_closed m ->
    forall p, RelationalPathBounds.closed_at (entry m) p.
  Proof.
    intros m [[Hcoh [Hzero [Htriangle Hstrong]]] Heven] p a b.
    destruct (entry m a p) as [left|] eqn:Hleft;
      destruct (entry m p b) as [right|] eqn:Hright;
      cbn [RelationalPathBounds.plus RelationalPathBounds.below];
      try (destruct (entry m a b); exact I).
    destruct (Htriangle a b p left right Hleft Hright)
      as [value [Hvalue Hle]]. rewrite Hvalue.
    cbn [RelationalPathBounds.below]. exact Hle.
  Qed.

  (** Adding paired zero diagonals preserves every triangle bound. *)
  Lemma add_zero_global_closed : forall m k,
    (forall p, RelationalPathBounds.closed_at (entry m) p) ->
    (forall p, entry m p p = None \/ entry m p p = Some 0%Z) ->
    forall p, RelationalPathBounds.closed_at
      (entry (add_cons k k 0%Z m)) p.
  Proof.
    intros m k Hclosed Hdiag.
    set (mid := put (flip k) (flip k)
      (lower_bound 0%Z (entry m (flip k) (flip k))) m).
    assert (Hmid : forall p, RelationalPathBounds.closed_at (entry mid) p).
    { intro p. unfold RelationalPathBounds.closed_at. intros a b.
      unfold mid. rewrite !entry_path_seed.
      exact (RelationalPathBounds.seed_global_closed K.t path_key_dec
        (entry m) (flip k) Hclosed (Hdiag (flip k)) p a b). }
    assert (Hmid_diag : entry mid k k = entry m k k).
    { unfold mid. rewrite entry_put.
      destruct (K.eqb_spec k (flip k)) as [Heq|Hne]; [|reflexivity].
      destruct k as [x sign]. destruct sign; discriminate Heq. }
    intro p. unfold RelationalPathBounds.closed_at. intros a b.
    change (RelationalPathBounds.below
      (entry (put k k (lower_bound 0%Z (entry m k k)) mid) a b)
      (RelationalPathBounds.plus
        (entry (put k k (lower_bound 0%Z (entry m k k)) mid) a p)
        (entry (put k k (lower_bound 0%Z (entry m k k)) mid) p b))).
    rewrite <- Hmid_diag. rewrite !entry_path_seed.
    assert (Hcase : entry mid k k = None \/ entry mid k k = Some 0%Z).
    { rewrite Hmid_diag. apply Hdiag. }
    exact (RelationalPathBounds.seed_global_closed K.t path_key_dec
      (entry mid) k Hmid Hcase p a b).
  Qed.

  Lemma incremental_seed_global_closed : forall m i j, tightly_closed m ->
    forall p, RelationalPathBounds.closed_at
      (entry (add_cons j j 0%Z (add_cons i i 0%Z m))) p.
  Proof.
    intros m i j Htight.
    assert (Hdiag : forall k, entry m k k = None \/ entry m k k = Some 0%Z).
    { now apply tightly_closed_diagonal_cases. }
    apply add_zero_global_closed.
    - apply add_zero_global_closed;
        [now apply tightly_closed_at_every_key|exact Hdiag].
    - now apply add_zero_diagonal_cases.
  Qed.

  (** Paired zero insertion gives every supported key a zero diagonal. *)
  Lemma add_zero_support_diagonal : forall m p,
    (forall k, entry m k k = None \/ entry m k k = Some 0%Z) ->
    (forall k, In (K.encode k) (support m) -> entry m k k = Some 0%Z) ->
    forall k, In (K.encode k) (support (add_cons p p 0%Z m)) ->
      entry (add_cons p p 0%Z m) k k = Some 0%Z.
  Proof.
    intros m p Hcases Hzero k Hsupport.
    rewrite support_add_cons in Hsupport.
    destruct Hsupport as [Hcode|[Hcode|[Hcode|[Hcode|Hcode]]]].
    - apply K.encode_inj in Hcode. subst k. now apply add_zero_own_diagonal.
    - apply K.encode_inj in Hcode. subst k. now apply add_zero_own_diagonal.
    - apply K.encode_inj in Hcode. subst k. now apply add_zero_flip_diagonal.
    - apply K.encode_inj in Hcode. subst k. now apply add_zero_flip_diagonal.
    - apply add_zero_preserve_diagonal; [exact Hcases|now apply Hzero].
  Qed.

  Lemma incremental_seed_zero_support : forall m i j, tightly_closed m ->
    forall k, In (K.encode k)
      (support (add_cons j j 0%Z (add_cons i i 0%Z m))) ->
      entry (add_cons j j 0%Z (add_cons i i 0%Z m)) k k = Some 0%Z.
  Proof.
    intros m i j Htight.
    assert (Hcases : forall k, entry m k k = None \/ entry m k k = Some 0%Z).
    { now apply tightly_closed_diagonal_cases. }
    apply add_zero_support_diagonal.
    - now apply add_zero_diagonal_cases.
    - apply add_zero_support_diagonal;
        [exact Hcases|exact (proj1 (proj2 (proj1 Htight)))].
  Qed.

  Lemma coordinate_flip : forall a b i j,
    same_coordinate (flip b) (flip a) i j =
    same_coordinate a b (flip j) (flip i).
  Proof.
    intros a b i j. unfold same_coordinate. rewrite !key_eqb_flip_left.
    apply andb_comm.
  Qed.

  (** Equal writes at mirrored coordinates preserve coherence on raw matrices. *)
  Lemma coherent_put_twins : forall i j d m,
    coherent m -> coherent (put i j d (put (flip j) (flip i) d m)).
  Proof.
    intros i j d m Hcoh a b.
    change (entry (put i j d (put (flip j) (flip i) d m)) a b =
      entry (put i j d (put (flip j) (flip i) d m)) (flip b) (flip a)).
    rewrite !entry_put_coordinate, !coordinate_flip, !flip_involutive.
    destruct (same_coordinate a b i j), (same_coordinate a b (flip j) (flip i));
      try reflexivity. exact (Hcoh a b).
  Qed.

  Lemma coherent_add_cons : forall i j d m,
    coherent m -> coherent (add_cons i j d m).
  Proof.
    intros i j d m Hcoh. unfold add_cons.
    assert (Hsame : entry m i j = entry m (flip j) (flip i)) by exact (Hcoh i j).
    rewrite <- Hsame. now apply coherent_put_twins.
  Qed.

  (** Constraint insertion adds both signs of both keys. *)
  Lemma bar_closed_add_cons : forall i j d m,
    bar_closed m -> bar_closed (add_cons i j d m).
  Proof.
    intros i j d m Hclosed k Hin. apply support_add_cons in Hin. apply support_add_cons.
    change (bar k) with (flip k).
    destruct Hin as [Hk | [Hk | [Hk | [Hk | Hk]]]].
    - apply K.encode_inj in Hk. subst k. right. right. now left.
    - apply K.encode_inj in Hk. subst k. right. right. right. now left.
    - apply K.encode_inj in Hk. subst k. rewrite flip_involutive. now left.
    - apply K.encode_inj in Hk. subst k. rewrite flip_involutive. right. now left.
    - right. right. right. right. now apply Hclosed.
  Qed.

  (** Constraint insertion writes both signed twins of a coherent matrix. *)
  Lemma F_add_cons_twins : forall i j d m, coherent m ->
    entry (add_cons i j d m) i j = entry (add_cons i j d m) (bar j) (bar i).
  Proof.
    intros i j d m Hcoh. exact (coherent_add_cons i j d m Hcoh i j).
  Qed.

  (** A strongly closed matrix is sign-closed. *)
  Lemma bar_closed_strong : forall m, strongly_closed m -> bar_closed m.
  Proof.
    intros m [Hcoh [Hdiag _]] i Hin.
    pose proof (Hdiag i Hin) as Hzero. rewrite (Hcoh i i) in Hzero.
    exact (entry_source_support m (bar i) (bar i) 0%Z Hzero).
  Qed.

  (** A tightened replacement changes only its unary coordinate. *)
  Definition tightened_other (m changed : dbm) : Prop :=
    forall i row, M.get i changed = Some row ->
      forall j, j <> flip i -> M.get j row = entry m i j.

  Lemma tighten_row_other : forall m changed k ignored,
    tightened_other m changed -> tightened_other m (tighten_row m changed k ignored).
  Proof.
    intros m changed k ignored Hchanged. unfold tighten_row.
    destruct (M.get k changed); [exact Hchanged|].
    destruct (M.get k m) as [row|] eqn:Hrow; [|exact Hchanged].
    destruct (M.get (flip k) row); [|exact Hchanged].
    intros i fresh Hfresh j Hother. rewrite get_set_cases in Hfresh.
    destruct (K.eqb_spec i k) as [Heq|Hne].
    - subst i. injection Hfresh as <-.
      rewrite M.get_set_other by exact Hother. unfold entry. now rewrite Hrow.
    - exact (Hchanged i fresh Hfresh j Hother).
  Qed.

  Lemma collected_tighten_other : forall m,
    tightened_other m (M.fold (tighten_row m) m M.empty).
  Proof.
    intro m. apply (fold_invariant _ _ (tightened_other m)).
    - intros i row Hrow. rewrite M.get_empty in Hrow. discriminate.
    - intros changed k ignored Hchanged. now apply tighten_row_other.
  Qed.

  Lemma entry_tighten_other : forall m i j, j <> flip i ->
    entry (tighten m) i j = entry m i j.
  Proof.
    intros m i j Hother. unfold entry at 1. unfold tighten.
    rewrite M.get_merge by reflexivity.
    destruct (M.get i m) as [row|] eqn:Hrow; cbn [replace_row].
    - destruct (M.get i (M.fold (tighten_row m) m M.empty)) as [fresh|] eqn:Hfresh.
      + exact (collected_tighten_other m i fresh Hfresh j Hother).
      + unfold entry. now rewrite Hrow.
    - unfold entry. now rewrite Hrow.
  Qed.

  (** Once a unary row is rounded, later callbacks leave that row intact. *)
  Lemma tighten_row_fixed : forall m changed i fresh k ignored,
    M.get i changed = Some fresh ->
    M.get i (tighten_row m changed k ignored) = Some fresh.
  Proof.
    intros m changed i fresh k ignored Hfresh. unfold tighten_row.
    destruct (K.eqb_spec k i) as [Heq|Hne].
    - subst k. now rewrite Hfresh.
    - destruct (M.get k changed) as [row|] eqn:Hrow; [exact Hfresh|].
      destruct (M.get k m) as [row|] eqn:Hsource; [|exact Hfresh].
      destruct (M.get (flip k) row) as [d|] eqn:Hunary; [|exact Hfresh].
      rewrite M.get_set_other by congruence. exact Hfresh.
  Qed.

  (** Visiting a source row rounds its unary entry exactly once. *)
  Lemma tighten_row_target : forall m changed i row d ignored,
    M.get i m = Some row -> M.get (flip i) row = Some d ->
    (M.get i changed = None \/
      M.get i changed = Some (M.set (flip i) (even_bound d) row)) ->
    M.get i (tighten_row m changed i ignored) =
      Some (M.set (flip i) (even_bound d) row).
  Proof.
    intros m changed i row d ignored Hrow Hd [Hnone|Hfixed].
    - unfold tighten_row. now rewrite Hnone, Hrow, Hd, M.get_set_same.
    - now apply tighten_row_fixed.
  Qed.

  Lemma tighten_row_unvisited : forall m changed i k ignored,
    i <> k -> M.get i changed = None ->
    M.get i (tighten_row m changed k ignored) = None.
  Proof.
    intros m changed i k ignored Hne Hnone. unfold tighten_row.
    destruct (M.get k changed) as [row|]; [exact Hnone|].
    destruct (M.get k m) as [row|]; [|exact Hnone].
    destruct (M.get (flip k) row) as [d|]; [|exact Hnone].
    rewrite M.get_set_other by exact Hne. exact Hnone.
  Qed.

  (** Tightening rounds every finite unary entry to its even predecessor. *)
  Lemma entry_tighten_unary : forall m, dbm_wf m -> forall i d,
    entry m i (flip i) = Some d ->
    entry (tighten m) i (flip i) = Some (even_bound d).
  Proof.
    intros m [Houter Hrows] i d Hentry.
    unfold entry in Hentry.
    destruct (M.get i m) as [row|] eqn:Hrow; [|discriminate].
    assert (Hin : In (i, row) (M.elements m)).
    { apply (proj2 (M.elements_spec (M.t Z) m i row Houter)). exact Hrow. }
    apply in_split in Hin. destruct Hin as [before [after Helems]].
    set (fresh := M.set (flip i) (even_bound d) row).
    assert (Hstep : forall changed k ignored,
      (M.get i changed = None \/ M.get i changed = Some fresh) ->
      M.get i (tighten_row m changed k ignored) = None \/
        M.get i (tighten_row m changed k ignored) = Some fresh).
    { intros changed k ignored [Hnone|Hfixed].
      - destruct (K.eqb_spec k i) as [Heq|Hne].
        + subst k. right. unfold fresh.
          eapply tighten_row_target; eauto.
        + left. apply tighten_row_unvisited; congruence.
      - right. now apply tighten_row_fixed. }
    assert (Hfold : forall xs changed,
      (M.get i changed = None \/ M.get i changed = Some fresh) ->
      M.get i (fold_left (fun acc kv => tighten_row m acc (fst kv) (snd kv))
        xs changed) = None \/
      M.get i (fold_left (fun acc kv => tighten_row m acc (fst kv) (snd kv))
        xs changed) = Some fresh).
    { induction xs as [|[k ignored] xs IH]; intros changed Hchanged;
        cbn [fold_left]; [exact Hchanged|].
      apply IH, Hstep, Hchanged. }
    assert (Hbefore : M.get i
      (fold_left (fun acc kv => tighten_row m acc (fst kv) (snd kv)) before M.empty) = None \/
      M.get i
      (fold_left (fun acc kv => tighten_row m acc (fst kv) (snd kv)) before M.empty) =
        Some fresh).
    { apply Hfold. left. apply M.get_empty. }
    assert (Hafter : forall xs changed,
      M.get i changed = Some fresh ->
      M.get i (fold_left (fun acc kv => tighten_row m acc (fst kv) (snd kv))
        xs changed) = Some fresh).
    { induction xs as [|[k ignored] xs IH]; intros changed Hfixed;
        cbn [fold_left]; [exact Hfixed|].
      apply IH. now apply tighten_row_fixed. }
    assert (Hcollected : M.get i (M.fold (tighten_row m) m M.empty) = Some fresh).
    { rewrite M.fold_spec, Helems, fold_left_app. cbn [fold_left].
      apply Hafter. eapply tighten_row_target; eauto. }
    unfold entry at 1, tighten. rewrite M.get_merge by reflexivity.
    rewrite Hrow, Hcollected. cbn [replace_row].
    unfold fresh. now rewrite M.get_set_same.
  Qed.

  Lemma entry_tighten_exact : forall m, dbm_wf m -> forall i j,
    entry (tighten m) i j =
      if K.eqb j (flip i) then option_map even_bound (entry m i j)
      else entry m i j.
  Proof.
    intros m Hwf i j. destruct (K.eqb_spec j (flip i)) as [Heq|Hne].
    - subst j.
      destruct (entry m i (flip i)) as [d|] eqn:Hentry.
      + now apply entry_tighten_unary.
      + destruct (entry (tighten m) i (flip i)) as [z|] eqn:Hnext;
          [|reflexivity].
        exfalso.
        assert (Hraw : raw_entry (tighten m) (K.encode i) (K.encode (flip i)) <>
          None).
        { rewrite raw_entry_get, Hnext. discriminate. }
        apply (proj1 (raw_tighten_presence m (K.encode i)
          (K.encode (flip i)))) in Hraw.
        rewrite raw_entry_get, Hentry in Hraw. exact (Hraw eq_refl).
    - now apply entry_tighten_other.
  Qed.

  Lemma tighten_unary_even : forall m, dbm_wf m -> forall i d,
    entry (tighten m) i (flip i) = Some d -> (d mod 2 = 0)%Z.
  Proof.
    intros m Hwf i d Hentry.
    rewrite entry_tighten_exact in Hentry by exact Hwf.
    destruct (K.eqb_spec (flip i) (flip i)) as [_|Hne]; [|contradiction].
    destruct (entry m i (flip i)) as [a|] eqn:Hsource; [|discriminate].
    inversion Hentry; subst d. unfold even_bound.
    replace (2 * Z.div2 a)%Z with (Z.div2 a * 2)%Z by ring.
    now rewrite Z.mod_mul by lia.
  Qed.

  Lemma entry_tighten_unary_option : forall m, dbm_wf m -> forall i,
    entry (tighten m) i (flip i) = option_map even_bound (entry m i (flip i)).
  Proof.
    intros m Hwf i. rewrite entry_tighten_exact by exact Hwf.
    destruct (K.eqb_spec (flip i) (flip i)) as [_|Hne];
      [reflexivity|contradiction].
  Qed.

  Lemma coherent_tighten : forall m, coherent m -> coherent (tighten m).
  Proof.
    intros m Hcoh i j.
    change (entry (tighten m) i j = entry (tighten m) (flip j) (flip i)).
    destruct (K.eqb_spec j (flip i)) as [Heq|Hne].
    - subst j. now rewrite flip_involutive.
    - rewrite entry_tighten_other by exact Hne.
      rewrite entry_tighten_other.
      + exact (Hcoh i j).
      + rewrite flip_involutive. congruence.
  Qed.

  Definition unary_twins (acc : M.t Z * M.t Z) : Prop :=
    forall k, M.get k (fst acc) = M.get (flip k) (snd acc).

  Lemma unary_maps_twins : forall m acc k ignored,
    unary_twins acc -> unary_twins (unary_maps m acc k ignored).
  Proof.
    intros m acc k ignored Htwins. unfold unary_maps.
    destruct (entry m k (flip k)); [|exact Htwins].
    intro q. cbn [fst snd]. rewrite !get_set_cases, key_eqb_flip_both.
    destruct (K.eqb q k); [reflexivity|apply Htwins].
  Qed.

  Lemma collect_unary_twins : forall m,
    unary_twins (M.fold (unary_maps m) m (M.empty, M.empty)).
  Proof.
    intro m. apply (fold_invariant _ _ unary_twins).
    - intro k. cbn [fst snd]. now rewrite !M.get_empty.
    - intros acc k ignored Htwins. now apply unary_maps_twins.
  Qed.

  Lemma collect_unary_left : forall m i d,
    M.get i (fst (M.fold (unary_maps m) m (M.empty, M.empty))) = Some d ->
    entry m i (flip i) = Some d.
  Proof.
    intros m i d Hget. rewrite M.get_find in Hget.
    destruct (collect_unary_origins m) as [Hleft _].
    destruct (Hleft (K.encode i) d Hget) as [k [Hkey Hsource]].
    apply K.encode_inj in Hkey. now subst k.
  Qed.

  (** Unary collection reads exactly the source matrix's finite unary entries. *)
  Lemma collect_unary_left_exact : forall m, dbm_wf m -> forall i,
    M.get i (fst (M.fold (unary_maps m) m (M.empty, M.empty))) =
      entry m i (flip i).
  Proof.
    intros m [Houter Hrows] i.
    destruct (entry m i (flip i)) as [d|] eqn:Hunary.
    - assert (Hfixed : forall acc k ignored,
        M.get i (fst acc) = Some d ->
        M.get i (fst (unary_maps m acc k ignored)) = Some d).
      { intros [left right] k ignored Hget. unfold unary_maps.
        destruct (entry m k (flip k)) as [z|] eqn:Hentry; [|exact Hget].
        cbn [fst]. destruct (K.eqb_spec k i) as [Heq|Hne].
        + subst k. rewrite Hunary in Hentry. inversion Hentry; subst z.
          now rewrite M.get_set_same.
        + rewrite M.get_set_other by congruence. exact Hget. }
      assert (Hhit : forall acc ignored,
        M.get i (fst (unary_maps m acc i ignored)) = Some d).
      { intros [left right] ignored. unfold unary_maps. rewrite Hunary.
        cbn [fst]. now rewrite M.get_set_same. }
      assert (Htail : forall xs acc,
        M.get i (fst acc) = Some d ->
        M.get i (fst (fold_left (fun state kv =>
          unary_maps m state (fst kv) (snd kv)) xs acc)) = Some d).
      { induction xs as [|[k ignored] xs IH]; intros acc Hget;
          cbn [fold_left]; [exact Hget|].
        apply IH, Hfixed, Hget. }
      unfold entry in Hunary.
      destruct (M.get i m) as [row|] eqn:Hrow; [|discriminate].
      assert (Hin : In (i, row) (M.elements m)).
      { apply (proj2 (M.elements_spec (M.t Z) m i row Houter)). exact Hrow. }
      apply in_split in Hin. destruct Hin as [before [after Helems]].
      rewrite M.fold_spec, Helems, fold_left_app. cbn [fold_left].
      apply Htail, Hhit.
    - assert (Hstep : forall acc k ignored,
        M.get i (fst acc) = None ->
        M.get i (fst (unary_maps m acc k ignored)) = None).
      { intros [left right] k ignored Hget. unfold unary_maps.
        destruct (entry m k (flip k)) as [z|] eqn:Hentry; [|exact Hget].
        cbn [fst]. destruct (K.eqb_spec k i) as [Heq|Hne].
        + subst k. congruence.
        + rewrite M.get_set_other by congruence. exact Hget. }
      apply (fold_invariant _ _
        (fun acc => M.get i (fst acc) = None));
        [cbn [fst]; apply M.get_empty|].
      intros acc k ignored Hget. now apply Hstep.
  Qed.

  (** The strengthened entry is the minimum with its collected unary average. *)
  Lemma entry_strengthen : forall m i j,
    entry (strengthen m) i j =
    match M.get i (fst (M.fold (unary_maps m) m (M.empty, M.empty))) with
    | Some a => strengthen_bound a (entry m i j)
        (M.get j (snd (M.fold (unary_maps m) m (M.empty, M.empty))))
    | None => entry m i j
    end.
  Proof.
    intros m i j. unfold entry at 1. unfold strengthen.
    rewrite M.get_merge by reflexivity.
    destruct (M.get i m) as [row|] eqn:Hrow; cbn [strengthen_outer].
    - destruct (M.get i (fst (M.fold (unary_maps m) m (M.empty, M.empty)))) as [a|].
      + rewrite M.get_merge by reflexivity. unfold entry. now rewrite Hrow.
      + unfold entry. now rewrite Hrow.
    - destruct (M.get i (fst (M.fold (unary_maps m) m (M.empty, M.empty))))
        as [a|] eqn:Ha.
      + pose proof (collect_unary_left m i a Ha) as Hsource.
        unfold entry in Hsource. rewrite Hrow in Hsource. discriminate.
      + unfold entry. now rewrite Hrow.
  Qed.

  (** Strengthening uses the source matrix's two unary bounds. *)
  Lemma entry_strengthen_exact : forall m, dbm_wf m -> forall i j,
    entry (strengthen m) i j =
      match entry m i (flip i) with
      | Some a => strengthen_bound a (entry m i j) (entry m (flip j) j)
      | None => entry m i j
      end.
  Proof.
    intros m Hwf i j. rewrite entry_strengthen.
    pose proof (collect_unary_twins m (flip j)) as Hright.
    rewrite flip_involutive in Hright. rewrite <- Hright.
    rewrite !collect_unary_left_exact by exact Hwf.
    now rewrite flip_involutive.
  Qed.

  Lemma entry_strengthen_unary : forall m, dbm_wf m -> forall i,
    entry (strengthen m) i (flip i) = entry m i (flip i).
  Proof.
    intros m Hwf i. rewrite entry_strengthen_exact by exact Hwf.
    rewrite flip_involutive.
    destruct (entry m i (flip i)) as [a|]; [|reflexivity].
    cbn [strengthen_bound lower_bound].
    replace (a + a)%Z with (2 * a)%Z by lia.
    rewrite Z.div2_div.
    replace (2 * a)%Z with (a * 2)%Z by ring.
    rewrite Z.div_mul by lia. now rewrite Z.min_id.
  Qed.

  Lemma strengthen_below_old : forall m, dbm_wf m -> forall i j,
    RelationalPathBounds.below (entry (strengthen m) i j) (entry m i j).
  Proof.
    intros m Hwf i j. rewrite entry_strengthen_exact by exact Hwf.
    destruct (entry m i (flip i)) as [a|]; [|apply RelationalPathBounds.below_refl].
    destruct (entry m (flip j) j) as [z|];
      destruct (entry m i j) as [old|]; cbn [strengthen_bound lower_bound
        RelationalPathBounds.below]; try exact I; lia.
  Qed.

  (** Strengthening enforces the unary average at every finite unary pair. *)
  Lemma strengthen_strong_clause : forall m, dbm_wf m ->
    forall i j a z,
      entry (strengthen m) i (flip i) = Some a ->
      entry (strengthen m) (flip j) j = Some z ->
      exists d, entry (strengthen m) i j = Some d /\ (2 * d <= a + z)%Z.
  Proof.
    intros m Hwf i j a z Hleft Hright.
    rewrite entry_strengthen_unary in Hleft by exact Hwf.
    assert (Hright' : entry (strengthen m) (flip j) (flip (flip j)) = Some z).
    { now rewrite flip_involutive. }
    rewrite entry_strengthen_unary in Hright' by exact Hwf.
    rewrite flip_involutive in Hright'.
    rewrite entry_strengthen_exact by exact Hwf.
    rewrite Hleft, Hright'. cbn [strengthen_bound].
    destruct (entry m i j) as [old|];
      [exists (Z.min (Z.div2 (a + z)) old)|exists (Z.div2 (a + z))];
      split; [reflexivity| |reflexivity|].
    - pose proof (Z.div_mod (a + z) 2 ltac:(lia)) as Hdiv.
      pose proof (Z.mod_pos_bound (a + z) 2 ltac:(lia)) as Hmod.
      rewrite Z.div2_div. lia.
    - pose proof (Z.div_mod (a + z) 2 ltac:(lia)) as Hdiv.
      pose proof (Z.mod_pos_bound (a + z) 2 ltac:(lia)) as Hmod.
      rewrite Z.div2_div. lia.
  Qed.

  Lemma coherent_strengthen : forall m, coherent m -> coherent (strengthen m).
  Proof.
    intros m Hcoh i j.
    change (entry (strengthen m) i j = entry (strengthen m) (flip j) (flip i)).
    rewrite !entry_strengthen.
    pose proof (collect_unary_twins m) as Htwins.
    rewrite (Htwins i), (Htwins (flip j)), flip_involutive.
    assert (Hsame : entry m i j = entry m (flip j) (flip i)) by exact (Hcoh i j).
    rewrite Hsame.
    destruct (M.get (flip i) (snd (M.fold (unary_maps m) m (M.empty, M.empty)))) as [a|],
      (M.get j (snd (M.fold (unary_maps m) m (M.empty, M.empty)))) as [b|];
      cbn [strengthen_bound]; try reflexivity.
    now rewrite Z.add_comm.
  Qed.

  (** Reversing a chain and flipping its endpoints preserves its weight. *)
  Lemma coherent_chain_pair : forall m i j ks,
    coherent m ->
    RelationalPathBounds.chain (entry m) i ks j =
      RelationalPathBounds.chain (entry m) (bar j) (map bar (rev ks)) (bar i).
  Proof.
    intros m i j ks Hcoh. revert i.
    induction ks as [|k ks IH]; intro i.
    - cbn [RelationalPathBounds.chain rev map]. apply Hcoh.
    - cbn [RelationalPathBounds.chain].
      cbn [rev]. rewrite map_app.
      cbn [map]. rewrite RelationalPathBounds.chain_app.
      cbn [RelationalPathBounds.chain].
      rewrite <- (IH k), (Hcoh i k).
      apply RelationalPathBounds.plus_comm.
  Qed.

  (** A sign-closed pivot set contains the paired chain of every witness. *)
  Lemma coherent_path_pair : forall m ps i j d,
    coherent m -> (forall k, In k ps -> In (bar k) ps) ->
    RelationalPathBounds.path_witness (entry m) ps i j d ->
    RelationalPathBounds.path_witness (entry m) ps (bar j) (bar i) d.
  Proof.
    intros m ps i j d Hcoh Hbar [Hzero|[ks [Hks Hchain]]].
    - left. destruct Hzero as [Heq Hd]. subst j d. now split.
    - right. exists (map bar (rev ks)). split.
      + intros k Hin. apply in_map_iff in Hin.
        destruct Hin as [p [Heq Hp]]. subst k.
        apply Hbar, Hks. now apply in_rev.
      + rewrite <- (coherent_chain_pair m i j ks Hcoh). exact Hchain.
  Qed.


  Local Definition path_sum (a b : option Z) : option Z :=
    match a, b with Some x, Some y => Some (x + y)%Z | _, _ => None end.

  Local Definition edge_path (d : Z) (a b : option Z) : option Z :=
    path_sum (edge_prefix d a) b.

  Local Definition twin_path (d : Z) (a cross b : option Z) : option Z :=
    path_sum (twin_prefix d a cross) b.

  Lemma relax_value_meet : forall prefix old exit,
    relax_value prefix old exit = bound_meet old (path_sum prefix exit).
  Proof.
    intros [a|] [z|] [b|]; cbn [relax_value via_bound lower_bound path_sum bound_meet];
      try reflexivity. f_equal. apply Z.min_comm.
  Qed.

  Lemma bound_meet_comm : forall a b, bound_meet a b = bound_meet b a.
  Proof.
    intros [a|] [b|]; cbn [bound_meet]; try reflexivity.
    f_equal. apply Z.min_comm.
  Qed.

  Lemma bound_meet_assoc : forall a b c,
    bound_meet (bound_meet a b) c = bound_meet a (bound_meet b c).
  Proof.
    intros [a|] [b|] [c|]; cbn [bound_meet]; try reflexivity.
    now rewrite Z.min_assoc.
  Qed.

  Lemma bound_meet_swap : forall old a b,
    bound_meet (bound_meet old a) b = bound_meet (bound_meet old b) a.
  Proof.
    intros old a b. rewrite !bound_meet_assoc. now rewrite (bound_meet_comm a b).
  Qed.

  Lemma edge_path_comm : forall d a b, edge_path d a b = edge_path d b a.
  Proof.
    intros d [a|] [b|]; cbn [edge_path path_sum edge_prefix]; try reflexivity.
    f_equal. ring.
  Qed.

  Lemma twin_path_comm : forall d a cross b,
    twin_path d a cross b = twin_path d b cross a.
  Proof.
    intros d [a|] [cross|] [b|]; cbn [twin_path path_sum twin_prefix]; try reflexivity.
    f_equal. ring.
  Qed.

  Lemma entry_increment : forall i j d m a b,
    entry (increment_matrix i j d m) a b =
    bound_meet
      (bound_meet
        (bound_meet
          (bound_meet (entry m a b)
            (edge_path d (entry m a i) (entry m j b)))
          (edge_path d (entry m a (flip j)) (entry m (flip i) b)))
        (twin_path d (entry m a i) (entry m j (flip j)) (entry m (flip i) b)))
      (twin_path d (entry m a (flip j)) (entry m (flip i) i) (entry m j b)).
  Proof.
    intros i j d m a b.
    rewrite <- (raw_entry_get (increment_matrix i j d m) a b).
    rewrite raw_entry_increment, !raw_entry_get, !relax_value_meet. reflexivity.
  Qed.

  (** Every incremental path relaxation retains or lowers the old entry. *)
  Lemma bound_meet_below_left : forall a b,
    RelationalPathBounds.below (bound_meet a b) a.
  Proof.
    intros [a|] [b|]; cbn [bound_meet RelationalPathBounds.below];
      try exact I; lia.
  Qed.

  Lemma bound_meet_below_right : forall a b,
    RelationalPathBounds.below (bound_meet a b) b.
  Proof.
    intros [a|] [b|]; cbn [bound_meet RelationalPathBounds.below];
      try exact I; lia.
  Qed.

  Lemma increment_entry_below : forall i j d m a b,
    RelationalPathBounds.below (entry (increment_matrix i j d m) a b)
      (entry m a b).
  Proof.
    intros i j d m a b. rewrite entry_increment.
    repeat (eapply RelationalPathBounds.below_trans;
      [apply bound_meet_below_left|]).
    apply RelationalPathBounds.below_refl.
  Qed.

  (** The candidate diagonal is bounded by either inserted signed edge. *)
  Lemma increment_below_first_edge : forall i j d m a b,
    RelationalPathBounds.below (entry (increment_matrix i j d m) a b)
      (edge_path d (entry m a i) (entry m j b)).
  Proof.
    intros i j d m a b. rewrite entry_increment.
    eapply RelationalPathBounds.below_trans;
      [apply bound_meet_below_left|].
    eapply RelationalPathBounds.below_trans;
      [apply bound_meet_below_left|].
    eapply RelationalPathBounds.below_trans;
      [apply bound_meet_below_left|].
    apply bound_meet_below_right.
  Qed.

  Lemma increment_below_second_edge : forall i j d m a b,
    RelationalPathBounds.below (entry (increment_matrix i j d m) a b)
      (edge_path d (entry m a (flip j)) (entry m (flip i) b)).
  Proof.
    intros i j d m a b. rewrite entry_increment.
    eapply RelationalPathBounds.below_trans;
      [apply bound_meet_below_left|].
    eapply RelationalPathBounds.below_trans;
      [apply bound_meet_below_left|].
    apply bound_meet_below_right.
  Qed.

  Lemma increment_below_first_twin : forall i j d m a b,
    RelationalPathBounds.below (entry (increment_matrix i j d m) a b)
      (twin_path d (entry m a i) (entry m j (flip j))
        (entry m (flip i) b)).
  Proof.
    intros i j d m a b. rewrite entry_increment.
    eapply RelationalPathBounds.below_trans;
      [apply bound_meet_below_left|].
    apply bound_meet_below_right.
  Qed.

  Lemma increment_below_second_twin : forall i j d m a b,
    RelationalPathBounds.below (entry (increment_matrix i j d m) a b)
      (twin_path d (entry m a (flip j)) (entry m (flip i) i)
        (entry m j b)).
  Proof.
    intros i j d m a b. rewrite entry_increment.
    apply bound_meet_below_right.
  Qed.

  (** A successful matrix scan checks every stored row label. *)
  Lemma matrix_ok_row : forall m k row, dbm_wf m ->
    matrix_ok m = true -> M.get k m = Some row -> nonnegative k m = true.
  Proof.
    intros m k row [Houter Hrows] Hscan Hrow.
    unfold matrix_ok in Hscan. rewrite M.fold_spec in Hscan.
    assert (Hfold : forall (es : list (K.t * M.t Z)) acc,
      fold_left (fun ok ka => andb ok (nonnegative (fst ka) m)) es acc =
        andb acc (forallb (fun ka => nonnegative (fst ka) m) es)).
    { induction es as [|[p value] es IH]; intro acc; [now destruct acc|].
      cbn [fold_left forallb]. rewrite IH. now rewrite andb_assoc. }
    rewrite Hfold in Hscan. cbn in Hscan.
    rewrite forallb_forall in Hscan. apply (Hscan (k, row)).
    apply (proj2 (M.elements_spec _ m k row Houter)). exact Hrow.
  Qed.

  Lemma matrix_ok_diagonal : forall m k z, dbm_wf m ->
    matrix_ok m = true -> entry m k k = Some z -> (0 <= z)%Z.
  Proof.
    intros m k z Hwf Hscan Hentry.
    assert (Hrow : exists row, M.get k m = Some row).
    { unfold entry in Hentry. destruct (M.get k m) as [row|] eqn:Hget;
        [now exists row|discriminate]. }
    destruct Hrow as [row Hrow].
    pose proof (matrix_ok_row m k row Hwf Hscan Hrow) as Hcheck.
    unfold nonnegative in Hcheck. rewrite Hentry in Hcheck.
    now apply Z.leb_le.
  Qed.

  (** A passing incremental scan excludes a negative cycle through the first edge. *)
  Lemma incremental_first_cycle : forall m i j d, dbm_wf m ->
    tightly_closed m ->
    let seed := add_cons j j 0%Z (add_cons i i 0%Z m) in
    matrix_ok (increment_matrix i j d seed) = true ->
    RelationalPathBounds.below (Some 0%Z)
      (RelationalPathBounds.plus (entry seed j i) (Some d)).
  Proof.
    intros m i j d Hwf Htight. cbn beta iota zeta.
    set (seed := add_cons j j 0%Z (add_cons i i 0%Z m)).
    set (next := increment_matrix i j d seed). intro Hscan.
    pose proof (proj1 (incremental_seed_diagonals m i j Htight)) as Hseed.
    change (entry seed i i = Some 0%Z) in Hseed.
    destruct (entry seed j i) as [back|] eqn:Hback; [|exact I].
    pose proof (increment_below_first_edge i j d seed i i) as Hbound.
    rewrite Hseed, Hback in Hbound.
    cbn [edge_path path_sum edge_prefix RelationalPathBounds.below] in Hbound.
    destruct (RelationalPathBounds.below_finite _ _ Hbound)
      as [value [Hvalue Hle]].
    change (entry next i i = Some value) in Hvalue.
    assert (Hwfseed : dbm_wf seed).
    { unfold seed. apply add_cons_wf, add_cons_wf. exact Hwf. }
    assert (Hwfnext : dbm_wf next).
    { unfold next. now apply increment_wf. }
    assert (Hrow : exists row, M.get i next = Some row).
    { unfold entry in Hvalue. destruct (M.get i next) as [row|] eqn:Hget;
        [now exists row|discriminate]. }
    destruct Hrow as [row Hrow].
    pose proof (matrix_ok_row next i row Hwfnext Hscan Hrow) as Hcheck.
    unfold nonnegative in Hcheck. rewrite Hvalue in Hcheck.
    apply Z.leb_le in Hcheck.
    cbn [RelationalPathBounds.plus RelationalPathBounds.below]. lia.
  Qed.

  (** The same scan excludes a negative cycle through the mirrored edge. *)
  Lemma incremental_second_cycle : forall m i j d, dbm_wf m ->
    tightly_closed m ->
    let seed := add_cons j j 0%Z (add_cons i i 0%Z m) in
    matrix_ok (increment_matrix i j d seed) = true ->
    RelationalPathBounds.below (Some 0%Z)
      (RelationalPathBounds.plus (entry seed (flip i) (flip j)) (Some d)).
  Proof.
    intros m i j d Hwf Htight. cbn beta iota zeta.
    set (seed := add_cons j j 0%Z (add_cons i i 0%Z m)).
    set (next := increment_matrix i j d seed). intro Hscan.
    assert (Hcoh : coherent seed).
    { unfold seed. apply coherent_add_cons, coherent_add_cons.
      exact (proj1 (proj1 Htight)). }
    pose proof (proj2 (incremental_seed_diagonals m i j Htight)) as Hj.
    change (entry seed j j = Some 0%Z) in Hj.
    assert (Hseed : entry seed (flip j) (flip j) = Some 0%Z).
    { rewrite (Hcoh (flip j) (flip j)), !flip_involutive. exact Hj. }
    destruct (entry seed (flip i) (flip j)) as [back|] eqn:Hback;
      [|exact I].
    pose proof (increment_below_second_edge i j d seed (flip j) (flip j))
      as Hbound.
    rewrite Hseed, Hback in Hbound.
    cbn [edge_path path_sum edge_prefix RelationalPathBounds.below] in Hbound.
    destruct (RelationalPathBounds.below_finite _ _ Hbound)
      as [value [Hvalue Hle]].
    change (entry next (flip j) (flip j) = Some value) in Hvalue.
    assert (Hwfseed : dbm_wf seed).
    { unfold seed. apply add_cons_wf, add_cons_wf. exact Hwf. }
    assert (Hwfnext : dbm_wf next).
    { unfold next. now apply increment_wf. }
    assert (Hrow : exists row, M.get (flip j) next = Some row).
    { unfold entry in Hvalue.
      destruct (M.get (flip j) next) as [row|] eqn:Hget;
        [now exists row|discriminate]. }
    destruct Hrow as [row Hrow].
    pose proof (matrix_ok_row next (flip j) row Hwfnext Hscan Hrow) as Hcheck.
    unfold nonnegative in Hcheck. rewrite Hvalue in Hcheck.
    apply Z.leb_le in Hcheck.
    cbn [RelationalPathBounds.plus RelationalPathBounds.below]. lia.
  Qed.

  (** A passing scan also excludes the cycle using both inserted edges. *)
  Lemma incremental_mixed_cycle : forall m i j d, dbm_wf m ->
    tightly_closed m ->
    let seed := add_cons j j 0%Z (add_cons i i 0%Z m) in
    matrix_ok (increment_matrix i j d seed) = true ->
    RelationalPathBounds.below (Some 0%Z)
      (twin_path d (Some 0%Z) (entry seed j (flip j))
        (entry seed (flip i) i)).
  Proof.
    intros m i j d Hwf Htight. cbn beta iota zeta.
    set (seed := add_cons j j 0%Z (add_cons i i 0%Z m)).
    set (next := increment_matrix i j d seed). intro Hscan.
    pose proof (proj1 (incremental_seed_diagonals m i j Htight)) as Hseed.
    change (entry seed i i = Some 0%Z) in Hseed.
    destruct (entry seed j (flip j)) as [cross|] eqn:Hcross;
      [|exact I].
    destruct (entry seed (flip i) i) as [back|] eqn:Hback;
      [|exact I].
    pose proof (increment_below_first_twin i j d seed i i) as Hbound.
    rewrite Hseed, Hcross, Hback in Hbound.
    cbn [twin_path path_sum twin_prefix RelationalPathBounds.below] in Hbound.
    destruct (RelationalPathBounds.below_finite _ _ Hbound)
      as [value [Hvalue Hle]].
    change (entry next i i = Some value) in Hvalue.
    assert (Hwfseed : dbm_wf seed).
    { unfold seed. apply add_cons_wf, add_cons_wf. exact Hwf. }
    assert (Hwfnext : dbm_wf next).
    { unfold next. now apply increment_wf. }
    pose proof (matrix_ok_diagonal next i value Hwfnext Hscan Hvalue) as Hz.
    cbn [twin_path path_sum twin_prefix RelationalPathBounds.below]. lia.
  Qed.

  (** The two sequential signed-edge extensions remain triangle closed. *)
  Lemma incremental_two_edge_closed : forall m i j d, dbm_wf m ->
    tightly_closed m ->
    let seed := add_cons j j 0%Z (add_cons i i 0%Z m) in
    matrix_ok (increment_matrix i j d seed) = true ->
    forall p, RelationalPathBounds.closed_at
      (RelationalPathBounds.edge_extension
        (RelationalPathBounds.edge_extension (entry seed) i j d)
        (flip j) (flip i) d) p.
  Proof.
    intros m i j d Hwf Htight. cbn beta iota zeta.
    set (seed := add_cons j j 0%Z (add_cons i i 0%Z m)). intro Hscan.
    pose proof (incremental_seed_global_closed m i j Htight) as Hseed.
    change (forall p, RelationalPathBounds.closed_at (entry seed) p) in Hseed.
    pose proof (incremental_first_cycle m i j d Hwf Htight Hscan) as Hfirst.
    pose proof (incremental_second_cycle m i j d Hwf Htight Hscan) as Hsecond.
    pose proof (incremental_mixed_cycle m i j d Hwf Htight Hscan) as Hmixed.
    change (RelationalPathBounds.below (Some 0%Z)
      (RelationalPathBounds.plus (entry seed j i) (Some d))) in Hfirst.
    change (RelationalPathBounds.below (Some 0%Z)
      (RelationalPathBounds.plus (entry seed (flip i) (flip j)) (Some d)))
      in Hsecond.
    change (RelationalPathBounds.below (Some 0%Z)
      (twin_path d (Some 0%Z) (entry seed j (flip j))
        (entry seed (flip i) i))) in Hmixed.
    assert (Hnew_cycle : RelationalPathBounds.below (Some 0%Z)
      (RelationalPathBounds.plus
        (RelationalPathBounds.edge_extension (entry seed) i j d
          (flip i) (flip j)) (Some d))).
    { unfold RelationalPathBounds.edge_extension.
      rewrite RelationalPathBounds.plus_minimum_r.
      apply RelationalPathBounds.minimum_glb. split; [exact Hsecond|].
      destruct (entry seed (flip i) i) as [back|] eqn:Hback;
        destruct (entry seed j (flip j)) as [cross|] eqn:Hcross;
        cbn [RelationalPathBounds.plus RelationalPathBounds.below
          twin_path path_sum twin_prefix] in *; try exact I; lia. }
    intro p. apply RelationalPathBounds.edge_extension_closed.
    - apply RelationalPathBounds.edge_extension_closed; [exact Hseed|exact Hfirst].
    - exact Hnew_cycle.
  Qed.

  (** The four candidate paths equal two sequential edge extensions. *)
  Lemma incremental_sequential_extension : forall m i j d,
    RelationalPathBounds.below (Some 0%Z)
      (twin_path d (Some 0%Z) (entry m j (flip j))
        (entry m (flip i) i)) ->
    forall a b, entry (increment_matrix i j d m) a b =
      RelationalPathBounds.edge_extension
        (RelationalPathBounds.edge_extension (entry m) i j d)
        (flip j) (flip i) d a b.
  Proof.
    intros m i j d Hmixed a b. rewrite entry_increment.
    unfold RelationalPathBounds.edge_extension, edge_path, twin_path,
      path_sum, edge_prefix, twin_prefix, bound_meet.
    destruct (entry m a b) as [old|];
      destruct (entry m a i) as [left|];
      destruct (entry m j b) as [right|];
      destruct (entry m a (flip j)) as [tleft|];
      destruct (entry m (flip i) b) as [tright|];
      destruct (entry m j (flip j)) as [cross|];
      destruct (entry m (flip i) i) as [back|];
      cbn [RelationalPathBounds.minimum RelationalPathBounds.plus
        RelationalPathBounds.below twin_path path_sum twin_prefix] in *;
      try reflexivity; try (f_equal; lia).
  Qed.

  (** A passing diagonal scan leaves the four-path candidate triangle closed. *)
  Lemma incremental_candidate_closed : forall m i j d, dbm_wf m ->
    tightly_closed m ->
    let seed := add_cons j j 0%Z (add_cons i i 0%Z m) in
    matrix_ok (increment_matrix i j d seed) = true ->
    forall p, RelationalPathBounds.closed_at
      (entry (increment_matrix i j d seed)) p.
  Proof.
    intros m i j d Hwf Htight. cbn beta iota zeta.
    set (seed := add_cons j j 0%Z (add_cons i i 0%Z m)). intro Hscan.
    pose proof (incremental_mixed_cycle m i j d Hwf Htight Hscan) as Hmixed.
    change (RelationalPathBounds.below (Some 0%Z)
      (twin_path d (Some 0%Z) (entry seed j (flip j))
        (entry seed (flip i) i))) in Hmixed.
    pose proof (incremental_two_edge_closed m i j d Hwf Htight Hscan)
      as Hclosed.
    change (forall p, RelationalPathBounds.closed_at
      (RelationalPathBounds.edge_extension
        (RelationalPathBounds.edge_extension (entry seed) i j d)
        (flip j) (flip i) d) p) in Hclosed.
    intro p. unfold RelationalPathBounds.closed_at. intros a b.
    rewrite !(incremental_sequential_extension seed i j d Hmixed).
    exact (Hclosed p a b).
  Qed.

  Lemma below_lower_bound : forall value d old,
    RelationalPathBounds.below value (Some d) ->
    RelationalPathBounds.below value old ->
    RelationalPathBounds.below value (Some (lower_bound d old)).
  Proof.
    intros [value|] d [old|]; cbn [lower_bound RelationalPathBounds.below];
      intros; try contradiction; lia.
  Qed.

  Lemma below_add_zero : forall m u p,
    (forall a b, RelationalPathBounds.below (u a b) (entry m a b)) ->
    u p p = Some 0%Z -> u (flip p) (flip p) = Some 0%Z ->
    forall a b, RelationalPathBounds.below
      (u a b) (entry (add_cons p p 0%Z m) a b).
  Proof.
    intros m u p Hbelow Hzero Hbar a b. rewrite entry_add_cons_coordinates.
    destruct (same_coordinate a b p p) eqn:Hfirst.
    - destruct (same_coordinate_true a b p p Hfirst) as [Ha Hb].
      subst a b. apply below_lower_bound;
        [rewrite Hzero; cbn [RelationalPathBounds.below]; lia|apply Hbelow].
    - destruct (same_coordinate a b (flip p) (flip p)) eqn:Hsecond.
      + destruct (same_coordinate_true a b (flip p) (flip p) Hsecond)
          as [Ha Hb]. subst a b.
        apply below_lower_bound;
          [rewrite Hbar; cbn [RelationalPathBounds.below]; lia|apply Hbelow].
      + apply Hbelow.
  Qed.

  (** Any closed lower relation lies below a one-edge extension. *)
  Lemma closed_below_edge_extension : forall (u base : K.t -> K.t -> option Z)
      i j d,
    (forall p, RelationalPathBounds.closed_at u p) ->
    (forall a b, RelationalPathBounds.below (u a b) (base a b)) ->
    RelationalPathBounds.below (u i j) (Some d) ->
    forall a b, RelationalPathBounds.below (u a b)
      (RelationalPathBounds.edge_extension base i j d a b).
  Proof.
    intros u base i j d Hclosed Hbelow Hedge a b.
    unfold RelationalPathBounds.edge_extension.
    apply RelationalPathBounds.minimum_glb. split; [apply Hbelow|].
    eapply RelationalPathBounds.below_trans; [apply (Hclosed i a b)|].
    apply RelationalPathBounds.plus_mono; [apply Hbelow|].
    eapply RelationalPathBounds.below_trans; [apply (Hclosed j i b)|].
    apply RelationalPathBounds.plus_mono; [exact Hedge|apply Hbelow].
  Qed.

  (** The four-path candidate is below direct twin insertion. *)
  Lemma incremental_candidate_below_direct : forall m i j d,
    tightly_closed m ->
    let seed := add_cons j j 0%Z (add_cons i i 0%Z m) in
    forall a b, RelationalPathBounds.below
      (entry (increment_matrix i j d seed) a b)
      (entry (add_cons i j d m) a b).
  Proof.
    intros m i j d Htight. cbn beta iota zeta.
    set (seed := add_cons j j 0%Z (add_cons i i 0%Z m)).
    set (next := increment_matrix i j d seed).
    destruct (incremental_seed_diagonals m i j Htight) as [Hii Hjj].
    change (entry seed i i = Some 0%Z) in Hii.
    change (entry seed j j = Some 0%Z) in Hjj.
    assert (Hcoh : coherent seed).
    { unfold seed. apply coherent_add_cons, coherent_add_cons.
      exact (proj1 (proj1 Htight)). }
    assert (Hbar_i : entry seed (flip i) (flip i) = Some 0%Z).
    { rewrite (Hcoh (flip i) (flip i)), !flip_involutive. exact Hii. }
    assert (Hbar_j : entry seed (flip j) (flip j) = Some 0%Z).
    { rewrite (Hcoh (flip j) (flip j)), !flip_involutive. exact Hjj. }
    assert (Hold : forall x y,
      RelationalPathBounds.below (entry next x y) (entry m x y)).
    { intros x y. eapply RelationalPathBounds.below_trans.
      - unfold next. apply increment_entry_below.
      - unfold seed. eapply RelationalPathBounds.below_trans;
          apply add_cons_entry_below. }
    assert (Hfirst : RelationalPathBounds.below (entry next i j) (Some d)).
    { unfold next. pose proof (increment_below_first_edge i j d seed i j) as Hbound.
      rewrite Hii, Hjj in Hbound.
      cbn [edge_path path_sum edge_prefix] in Hbound.
      replace (0 + d + 0)%Z with d in Hbound by lia. exact Hbound. }
    assert (Hsecond : RelationalPathBounds.below
      (entry next (flip j) (flip i)) (Some d)).
    { unfold next.
      pose proof (increment_below_second_edge i j d seed (flip j) (flip i))
        as Hbound.
      rewrite Hbar_j, Hbar_i in Hbound.
      cbn [edge_path path_sum edge_prefix] in Hbound.
      replace (0 + d + 0)%Z with d in Hbound by lia. exact Hbound. }
    intros a b. rewrite entry_add_cons_coordinates.
    destruct (same_coordinate a b i j) eqn:Hcoordinate.
    - destruct (same_coordinate_true a b i j Hcoordinate) as [Ha Hb].
      subst a b. apply below_lower_bound; [exact Hfirst|apply Hold].
    - destruct (same_coordinate a b (flip j) (flip i)) eqn:Hmirror.
      + destruct (same_coordinate_true a b (flip j) (flip i) Hmirror)
          as [Ha Hb]. subst a b.
        apply below_lower_bound; [exact Hsecond|apply Hold].
      + apply Hold.
  Qed.

  (** The scan and seed zeros fix every candidate support diagonal at zero. *)
  Lemma incremental_candidate_zero_support : forall m i j d,
    dbm_wf m -> tightly_closed m ->
    let seed := add_cons j j 0%Z (add_cons i i 0%Z m) in
    matrix_ok (increment_matrix i j d seed) = true ->
    forall k, In (K.encode k) (support seed) ->
      entry (increment_matrix i j d seed) k k = Some 0%Z.
  Proof.
    intros m i j d Hwf Htight. cbn beta iota zeta.
    set (seed := add_cons j j 0%Z (add_cons i i 0%Z m)).
    set (next := increment_matrix i j d seed). intros Hscan k Hsupport.
    pose proof (incremental_seed_zero_support m i j Htight k Hsupport)
      as Hseed.
    change (entry seed k k = Some 0%Z) in Hseed.
    pose proof (increment_entry_below i j d seed k k) as Hbound.
    rewrite Hseed in Hbound.
    destruct (RelationalPathBounds.below_finite _ _ Hbound)
      as [value [Hvalue Hle]].
    change (entry next k k = Some value) in Hvalue.
    assert (Hwfseed : dbm_wf seed).
    { unfold seed. apply add_cons_wf, add_cons_wf. exact Hwf. }
    assert (Hwfnext : dbm_wf next).
    { unfold next. now apply increment_wf. }
    pose proof (matrix_ok_diagonal next k value Hwfnext Hscan Hvalue) as Hz.
    assert (value = 0)%Z by lia. now subst value.
  Qed.

  (** A closed lower relation remains below every Floyd round. *)
  Lemma fw_round_above_closed : forall u current k,
    (forall p, RelationalPathBounds.closed_at u p) ->
    (forall a b, RelationalPathBounds.below (u a b) (entry current a b)) ->
    u k k = Some 0%Z -> pivot_present k current = true ->
    forall a b, RelationalPathBounds.below
      (u a b) (entry (fw_round k current) a b).
  Proof.
    intros u current k Hclosed Hbelow Hzero Hpresent a b.
    rewrite (entry_fw_present k current Hpresent a b).
    apply (RelationalPathBounds.floyd_above_closed K.t path_key_dec
      u (entry current) k Hclosed Hbelow Hzero a b).
  Qed.

  Lemma fw_pivots_above_closed : forall ks current u,
    (forall k, In k ks -> In (K.encode k) (support current)) ->
    (forall k, In k ks -> u k k = Some 0%Z) ->
    (forall p, RelationalPathBounds.closed_at u p) ->
    (forall a b, RelationalPathBounds.below (u a b) (entry current a b)) ->
    forall a b, RelationalPathBounds.below
      (u a b) (entry (fw_pivots ks current) a b).
  Proof.
    induction ks as [|k ks IH]; intros current u Hsupport Hzero Hclosed Hbelow a b.
    - exact (Hbelow a b).
    - assert (Hpresent : pivot_present k current = true).
      { apply pivot_present_support. apply Hsupport. now left. }
      assert (Hnext : forall x y, RelationalPathBounds.below
        (u x y) (entry (fw_round k current) x y)).
      { intros x y. eapply fw_round_above_closed;
          [exact Hclosed|exact Hbelow|apply Hzero; now left|exact Hpresent]. }
      assert (Haccept : nonnegative k (fw_round k current) = true).
      { unfold nonnegative. destruct (entry (fw_round k current) k k) as [z|]
          eqn:Hentry; [|reflexivity].
        pose proof (Hnext k k) as Hbound. rewrite (Hzero k (or_introl eq_refl)),
          Hentry in Hbound.
        apply Z.leb_le. exact Hbound. }
      cbn [fw_pivots]. rewrite Haccept.
      apply IH.
      + intros q Hq. apply (proj2 (support_round k current (K.encode q))).
        apply Hsupport. now right.
      + intros q Hq. apply Hzero. now right.
      + exact Hclosed.
      + exact Hnext.
  Qed.

  Lemma direct_seed_support : forall m i j d p,
    In p (support (add_cons i j d m)) <->
      In p (support (add_cons j j 0%Z (add_cons i i 0%Z m))).
  Proof.
    intros m i j d p. rewrite !support_add_cons. tauto.
  Qed.

  (** Successful incremental closure bounds the full Floyd matrix below it. *)
  Lemma incremental_candidate_below_fw : forall m i j d,
    dbm_wf m -> tightly_closed m ->
    let direct := add_cons i j d m in
    let seed := add_cons j j 0%Z (add_cons i i 0%Z m) in
    matrix_ok (increment_matrix i j d seed) = true ->
    forall a b, RelationalPathBounds.below
      (entry (increment_matrix i j d seed) a b) (entry (fw direct) a b).
  Proof.
    intros m i j d Hwf Htight. cbn beta iota zeta.
    set (direct := add_cons i j d m).
    set (seed := add_cons j j 0%Z (add_cons i i 0%Z m)).
    set (next := increment_matrix i j d seed). intro Hscan.
    assert (Hwfdirect : dbm_wf direct).
    { unfold direct. now apply add_cons_wf. }
    assert (Hclosed : forall p, RelationalPathBounds.closed_at (entry next) p).
    { unfold next, seed. now apply incremental_candidate_closed. }
    assert (Hbelow : forall x y,
      RelationalPathBounds.below (entry next x y) (entry direct x y)).
    { intros x y. unfold next, seed, direct.
      now apply incremental_candidate_below_direct. }
    assert (Hzero : forall k, In k (keys direct) -> entry next k k = Some 0%Z).
    { intros k Hkey. unfold next.
      apply (incremental_candidate_zero_support m i j d Hwf Htight Hscan).
      change (In (K.encode k) (support seed)).
      apply (proj1 (direct_seed_support m i j d (K.encode k))).
      unfold direct in Hkey. now apply keys_support. }
    intros a b. unfold fw. rewrite pivot_keys_eq_keys.
    apply fw_pivots_above_closed.
    - intros k Hkey. now apply keys_support.
    - exact Hzero.
    - exact Hclosed.
    - exact Hbelow.
  Qed.

  Lemma incremental_candidate_fw_scan : forall m i j d,
    dbm_wf m -> tightly_closed m ->
    let direct := add_cons i j d m in
    let seed := add_cons j j 0%Z (add_cons i i 0%Z m) in
    matrix_ok (increment_matrix i j d seed) = true ->
    forallb (fun k => nonnegative k (fw direct)) (keys direct) = true.
  Proof.
    intros m i j d Hwf Htight. cbn beta iota zeta.
    set (direct := add_cons i j d m).
    set (seed := add_cons j j 0%Z (add_cons i i 0%Z m)).
    set (next := increment_matrix i j d seed). intro Hscan.
    assert (Hwfdirect : dbm_wf direct).
    { unfold direct. now apply add_cons_wf. }
    apply forallb_forall. intros k Hkey.
    assert (Hsupport : In (K.encode k) (support seed)).
    { apply (proj1 (direct_seed_support m i j d (K.encode k))).
      unfold direct in Hkey. now apply keys_support. }
    pose proof (incremental_candidate_zero_support m i j d Hwf Htight
      Hscan k Hsupport) as Hzero.
    change (entry next k k = Some 0%Z) in Hzero.
    pose proof (incremental_candidate_below_fw m i j d Hwf Htight Hscan k k)
      as Hbound.
    change (RelationalPathBounds.below (entry next k k)
      (entry (fw direct) k k)) in Hbound.
    unfold nonnegative. destruct (entry (fw direct) k k) as [z|]
      eqn:Hentry; [|reflexivity].
    rewrite Hzero in Hbound.
    apply Z.leb_le. exact Hbound.
  Qed.

  Lemma coherent_entry : forall m, coherent m ->
    forall a b, entry m a b = entry m (flip b) (flip a).
  Proof.
    intros m Hcoh. exact Hcoh.
  Qed.

  (** Mirroring exchanges the two single-edge paths and reverses each mixed path. *)
  Lemma coherent_increment : forall i j d m,
    coherent m -> coherent (increment_matrix i j d m).
  Proof.
    intros i j d m Hcoh a b.
    change (entry (increment_matrix i j d m) a b =
      entry (increment_matrix i j d m) (flip b) (flip a)).
    rewrite !entry_increment.
    rewrite (coherent_entry m Hcoh (flip b) i),
      (coherent_entry m Hcoh (flip b) (flip j)),
      (coherent_entry m Hcoh j (flip a)),
      (coherent_entry m Hcoh (flip i) (flip a)), !flip_involutive.
    rewrite <- (coherent_entry m Hcoh a b).
    rewrite (edge_path_comm d (entry m (flip i) b) (entry m a (flip j))),
      (edge_path_comm d (entry m j b) (entry m a i)),
      (twin_path_comm d (entry m (flip i) b) (entry m j (flip j)) (entry m a i)),
      (twin_path_comm d (entry m j b) (entry m (flip i) i) (entry m a (flip j))).
    rewrite (bound_meet_swap (entry m a b)
      (edge_path d (entry m a i) (entry m j b))
      (edge_path d (entry m a (flip j)) (entry m (flip i) b))).
    reflexivity.
  Qed.

  Lemma coh_incr_close : forall i j d m, coherent m -> coh (incr_close i j d m).
  Proof.
    intros i j d m Hcoh. unfold incr_close.
    set (seed := add_cons j j 0%Z (add_cons i i 0%Z m)).
    change (coh (if matrix_ok (increment_matrix i j d seed) then
      if matrix_ok (strengthen (tighten (increment_matrix i j d seed))) then
        Reached (strengthen (tighten (increment_matrix i j d seed))) else Unreached
      else Unreached)).
    destruct (matrix_ok (increment_matrix i j d seed)); [|exact I].
    destruct (matrix_ok (strengthen (tighten (increment_matrix i j d seed)))); [|exact I].
    cbn [coh]. apply coherent_strengthen, coherent_tighten, coherent_increment.
    unfold seed. now apply coherent_add_cons, coherent_add_cons.
  Qed.


  Lemma coh_refine : forall i j d s, coh s -> coh (refine i j d s).
  Proof.
    intros i j d [|m] Hcoh; [exact I|].
    cbn [refine coh] in *. now apply coh_incr_close.
  Qed.

  Lemma variable_offset_flip : forall x d i,
    variable_offset x d (flip i) = (- variable_offset x d i)%Z.
  Proof.
    intros x d [y sign]. unfold variable_offset, flip. cbn [fst snd].
    destruct (X.eqb y x), sign; cbn -[Z.opp]; ring.
  Qed.

  Lemma coherent_shift : forall x d m, coherent m -> coherent (shift x d m).
  Proof.
    intros x d m Hcoh i j.
    change (entry (shift x d m) i j = entry (shift x d m) (flip j) (flip i)).
    rewrite !entry_shift, !variable_offset_flip, (coherent_entry m Hcoh i j).
    destruct (entry m (flip j) (flip i)); cbn [option_map]; [f_equal; ring|reflexivity].
  Qed.

  Lemma coh_assign_copy : forall x source d s,
    coh s -> coh (assign_copy x source d s).
  Proof.
    intros x source d [|m] Hcoh; [exact I|]. cbn [assign_copy].
    destruct (K.eqb source (x, true)).
    - cbn [coh]. now apply coherent_shift.
    - apply coh_refine, coh_refine, coh_havoc, Hcoh.
  Qed.

  Lemma coh_add_range : forall x bounds s, coh s -> coh (add_range x bounds s).
  Proof.
    intros x [lo hi] s Hcoh. destruct lo, hi; cbn [add_range fst snd];
      repeat apply coh_refine; exact Hcoh.
  Qed.

  Lemma copied_literal_flip : forall x source i,
    copied_literal x source (flip i) = flip (copied_literal x source i).
  Proof.
    intros x source [y sign]. unfold copied_literal, flip. cbn [fst snd].
    destruct (X.eqb y x), sign; cbn [fst snd negb];
      [reflexivity|destruct source as [z polarity]; destruct polarity; reflexivity|
        reflexivity|reflexivity].
  Qed.

  Lemma coherent_copy_literals : forall x source d m, fst source <> x ->
    coherent m -> coherent (copy_literals x source d m).
  Proof.
    intros x source d m Hsource Hcoh i j.
    change (entry (copy_literals x source d m) i j =
      entry (copy_literals x source d m) (flip j) (flip i)).
    rewrite !entry_copy_literals by exact Hsource.
    rewrite !variable_offset_flip, !copied_literal_flip.
    rewrite (coherent_entry m Hcoh (copied_literal x source i) (copied_literal x source j)).
    destruct (entry m (flip (copied_literal x source j))
      (flip (copied_literal x source i))); cbn [option_map];
      [f_equal; ring|reflexivity].
  Qed.

  Lemma coh_assign_copy_fast : forall x source d s,
    copy_allowed x source = true -> coh s -> coh (assign_copy_fast x source d s).
  Proof.
    intros x source d [|m] Hallowed Hcoh; [exact I|]. cbn [assign_copy_fast].
    destruct (K.eqb_spec source (x, true)) as [Heq|Hneq].
    - cbn [coh]. now apply coherent_shift.
    - cbn [coh]. apply coherent_copy_literals.
      + destruct (copy_allowed_spec x source Hallowed); [contradiction|assumption].
      + now apply coherent_add_cons.
  Qed.

  Lemma collect_unary_row_none : forall m i, M.get i m = None ->
    M.get i (fst (M.fold (unary_maps m) m (M.empty, M.empty))) = None.
  Proof.
    intros m i Hnone.
    destruct (M.get i (fst (M.fold (unary_maps m) m (M.empty, M.empty))))
      as [d|] eqn:Hget; [|reflexivity].
    apply collect_unary_left in Hget. unfold entry in Hget.
    rewrite Hnone in Hget. discriminate Hget.
  Qed.

  Lemma literal_key_eqb : forall x y sign polarity,
    K.eqb (x, sign) (y, polarity) =
      if X.eqb x y then Bool.eqb sign polarity else false.
  Proof.
    intros x y sign polarity.
    destruct (X.eqb_spec x y), (K.eqb_spec (x, sign) (y, polarity));
      destruct sign, polarity; cbn; congruence.
  Qed.

  Lemma entry_range_columns : forall x lower upper m i j,
    entry (M.merge (range_column_row x lower upper) m
      (fst (M.fold (unary_maps m) m (M.empty, M.empty)))) i j =
    if X.eqb (fst j) x then
      range_average (if snd j then upper else lower)
        (M.get i (fst (M.fold (unary_maps m) m (M.empty, M.empty)))) None
    else entry m i j.
  Proof.
    intros x lower upper m i [y sign].
    unfold entry at 1. rewrite M.get_merge by reflexivity.
    destruct (M.get i m) as [row|] eqn:Hrow.
    - cbn [range_column_row]. rewrite !get_put_bound, !literal_key_eqb.
      unfold entry. rewrite Hrow. cbn [fst snd].
      destruct (X.eqb y x), sign; reflexivity.
    - cbn [range_column_row]. rewrite (collect_unary_row_none m i Hrow).
      unfold entry. rewrite Hrow. cbn [fst snd].
      destruct (X.eqb y x), sign, lower, upper; reflexivity.
  Qed.

  (** The new matrix retains old edges away from the assigned variable. *)
  Lemma entry_range_matrix : forall x lower upper m i j,
    let unaries := M.fold (unary_maps m) m (M.empty, M.empty) in
    entry (range_matrix x lower upper m) i j =
      if X.eqb (fst i) x then
        if X.eqb (fst j) x then
          if Bool.eqb (snd i) (snd j) then Some 0%Z
          else if snd i then lower else upper
        else range_average (if snd i then lower else upper) (M.get j (snd unaries)) None
      else if X.eqb (fst j) x then
        range_average (if snd j then upper else lower) (M.get i (fst unaries)) None
      else entry m i j.
  Proof.
    intros x lower upper m [a sa] [b sb]. cbn [fst snd].
    unfold range_matrix, entry at 1. rewrite !get_set_cases, !literal_key_eqb.
    destruct (X.eqb a x) eqn:Ha; destruct sa; cbn [Bool.eqb].
    - rewrite get_range_literal_row, !literal_key_eqb. cbn [negb].
      destruct (X.eqb b x), sb; reflexivity.
    - rewrite get_range_literal_row, !literal_key_eqb. cbn [negb].
      destruct (X.eqb b x), sb; reflexivity.
    - fold (entry (M.merge (range_column_row x lower upper) m
        (fst (M.fold (unary_maps m) m (M.empty, M.empty)))) (a, true) (b, sb)).
      apply entry_range_columns.
    - fold (entry (M.merge (range_column_row x lower upper) m
        (fst (M.fold (unary_maps m) m (M.empty, M.empty)))) (a, false) (b, sb)).
      apply entry_range_columns.
  Qed.

  Lemma coherent_range_matrix : forall x lower upper m,
    coherent m -> coherent (range_matrix x lower upper m).
  Proof.
    intros x lower upper m Hcoh i j.
    change (entry (range_matrix x lower upper m) i j =
      entry (range_matrix x lower upper m) (flip j) (flip i)).
    rewrite !entry_range_matrix.
    pose proof (collect_unary_twins m) as Htwins. unfold unary_twins in Htwins.
    rewrite !Htwins, !flip_involutive.
    destruct i as [a sa], j as [b sb]. cbn [flip fst snd].
    destruct (X.eqb a x), (X.eqb b x); destruct sa, sb;
      cbn [negb Bool.eqb]; try reflexivity; apply Hcoh.
  Qed.

  Lemma coh_add_range_fast : forall x bounds s, coh s -> coh (add_range_fast x bounds s).
  Proof.
    intros x [lo hi] [|m] Hcoh; [exact I|].
    destruct lo as [|lo|], hi as [|hi|]; cbn [add_range_fast coh];
      try exact I; try exact Hcoh; try (now apply coherent_range_matrix).
    destruct (lo <=? hi)%Z; [now apply coherent_range_matrix|exact I].
  Qed.

  Lemma coh_assign : forall x e s, coh s -> coh (assign x e s).
  Proof.
    intros x e [|m] Hcoh; [exact I|]. cbn [assign].
    destruct (F.lin_of e) as [[f r]|]; [|now apply coh_havoc].
    destruct (copy_source f) as [source|].
    - destruct (copy_allowed x source) eqn:Hallowed; cbn beta iota zeta.
      + destruct (rel_wrap_exact r (form_bounds m f)).
        * now apply coh_assign_copy_fast.
        * apply coh_add_range_fast, coh_havoc, Hcoh.
      + apply coh_add_range_fast, coh_havoc, Hcoh.
    - apply coh_add_range_fast, coh_havoc, Hcoh.
  Qed.

  Lemma coh_assume_cmp : forall c shape d s, coh s -> coh (assume_cmp c shape d s).
  Proof.
    intros c [|i j double] d s Hcoh.
    - cbn [assume_cmp].
      destruct (match c with CLe => (0 <=? d)%Z | CLt => (0 <? d)%Z |
        CEq => (0 =? d)%Z end); [exact Hcoh|exact I].
    - destruct c; cbn [assume_cmp]; repeat apply coh_refine; exact Hcoh.
  Qed.

  Lemma coh_assume_atom : forall s a, coh s -> coh (assume_atom s a).
  Proof.
    intros [|m] a Hcoh; [exact I|]. cbn [assume_atom].
    destruct (difference_forms (al a) (ar a)) as [shape|]; [|exact Hcoh].
    destruct (andb (form_exact m (al a) (alw a)) (form_exact m (ar a) (arw a)));
      [now apply coh_assume_cmp|exact Hcoh].
  Qed.

  Lemma coh_assume_atoms : forall atoms s,
    coh s -> coh (fold_left assume_atom atoms s).
  Proof.
    intro atoms. induction atoms as [|a atoms IH]; intros s Hcoh; cbn [fold_left].
    - exact Hcoh.
    - apply IH, coh_assume_atom, Hcoh.
  Qed.

  Lemma coh_assume : forall g es s, coh s -> coh (assume g es s).
  Proof.
    intros g es [|m] Hcoh; [exact I|]. cbn [assume]. now apply coh_assume_atoms.
  Qed.


  Definition option_weight {A : Type} (w : A -> nat) (a : option A) : nat :=
    match a with Some x => w x | None => 0 end.

  (** Summed weights account for stored payloads independently of their labels. *)
  Definition sum_weight {A : Type} (w : A -> nat) (xs : list A) : nat :=
    fold_right Nat.add 0 (map w xs).

  (** A map's payload weight ranges over its distinct stored codes. *)
  Definition stored_weight {A : Type} (w : A -> nat) (m : M.t A) : nat :=
    sum_weight (fun p => option_weight w (M.find p m)) (M.codes m).

  (** A sparse map pays for its skeleton, bindings, and stored payloads separately. *)
  Definition code_work {A : Type} (w : A -> nat) (m : M.t A) : nat :=
    M.nodes m + length (M.codes m) + stored_weight w m.

  (** List concatenation adds the two weight sums. *)
  Lemma sum_weight_app : forall (A : Type) (w : A -> nat) xs ys,
    sum_weight w (xs ++ ys) = sum_weight w xs + sum_weight w ys.
  Proof.
    intros A w xs. induction xs as [|x xs IH]; intro ys.
    - reflexivity.
    - change (w x + sum_weight w (xs ++ ys) =
        w x + sum_weight w xs + sum_weight w ys). rewrite IH. lia.
  Qed.

  (** Pointwise addition distributes over the weight sum. *)
  Lemma sum_weight_add : forall (A : Type) (f g : A -> nat) xs,
    sum_weight (fun x => f x + g x) xs = sum_weight f xs + sum_weight g xs.
  Proof.
    intros A f g xs. induction xs as [|x xs IH].
    - reflexivity.
    - change (f x + g x + sum_weight (fun y => f y + g y) xs =
        f x + sum_weight f xs + (g x + sum_weight g xs)). rewrite IH. lia.
  Qed.

  (** Unit weights count list members. *)
  Lemma sum_weight_one : forall (A : Type) (xs : list A),
    sum_weight (fun _ => 1) xs = length xs.
  Proof.
    intros A xs. induction xs as [|x xs IH]; [reflexivity|].
    change (1 + sum_weight (fun _ : A => 1) xs = S (length xs)). now rewrite IH.
  Qed.

  (** A duplicate-free sublist cannot have a larger nonnegative weight sum. *)
  Lemma sum_weight_incl : forall (A : Type) (w : A -> nat) xs ys,
    NoDup xs -> incl xs ys -> sum_weight w xs <= sum_weight w ys.
  Proof.
    intros A w xs. induction xs as [|x xs IH]; intros ys Hnodup Hincl.
    - change (0 <= sum_weight w ys). lia.
    - apply NoDup_cons_iff in Hnodup. destruct Hnodup as [Hfresh Hnodup].
      assert (Hx : In x ys) by (apply Hincl; now left).
      apply in_split in Hx. destruct Hx as [before [after Heq]]. subst ys.
      assert (Hrest : incl xs (before ++ after)).
      { intros y Hy. specialize (Hincl y (or_intror Hy)).
        apply in_app_iff in Hincl. apply in_app_iff.
        destruct Hincl as [Hin | [Heq | Hin]].
        - now left.
        - subst y. contradiction.
        - now right. }
      pose proof (IH (before ++ after) Hnodup Hrest) as Hsum.
      rewrite !sum_weight_app in Hsum |- *.
      change (w x + sum_weight w xs <=
        sum_weight w before + (w x + sum_weight w after)). lia.
  Qed.

  (** Removing absent lookups does not change their summed payload weight. *)
  Lemma sum_lookup_filter : forall (A : Type) (w : A -> nat) (m : M.t A) xs,
    sum_weight (fun p => option_weight w (M.find p m)) xs =
    sum_weight (fun p => option_weight w (M.find p m))
      (filter (fun p => match M.find p m with Some _ => true | None => false end) xs).
  Proof.
    intros A w m xs. unfold sum_weight. induction xs as [|p xs IH]; [reflexivity|].
    cbn [map fold_right filter]. destruct (M.find p m) eqn:Hlookup;
      cbn [option_weight map fold_right]; rewrite ?Hlookup;
      cbn [option_weight]; now rewrite IH.
  Qed.

  (** Looking up distinct codes can charge each stored payload at most once. *)
  Lemma stored_weight_bound : forall (A : Type) (w : A -> nat) (m : M.t A) xs,
    NoDup xs -> sum_weight (fun p => option_weight w (M.find p m)) xs <=
      stored_weight w m.
  Proof.
    intros A w m xs Hnodup. rewrite sum_lookup_filter. unfold stored_weight.
    apply sum_weight_incl.
    - now apply NoDup_filter.
    - intros p Hin. apply filter_In in Hin. destruct Hin as [_ Hpresent].
      apply M.codes_spec. destruct (M.find p m); congruence.
  Qed.

  (** Scanning both code lists charges each payload at most twice. *)
  Lemma pair_stored_weight_bound : forall (A B : Type) (wa : A -> nat) (wb : B -> nat)
      (ma : M.t A) (mb : M.t B),
    sum_weight (fun p => option_weight wa (M.find p ma) +
      option_weight wb (M.find p mb) + 1) (M.codes ma ++ M.codes mb) <=
    2 * stored_weight wa ma + 2 * stored_weight wb mb +
      length (M.codes ma) + length (M.codes mb).
  Proof.
    intros A B wa wb ma mb.
    pose proof (stored_weight_bound A wa ma (M.codes mb) (M.codes_nodup B mb)) as Ha.
    pose proof (stored_weight_bound B wb mb (M.codes ma) (M.codes_nodup A ma)) as Hb.
    rewrite sum_weight_app. repeat rewrite sum_weight_add. rewrite !sum_weight_one.
    unfold stored_weight in *. lia.
  Qed.

  (** Pointwise callback bounds sum to the corresponding weighted list bound. *)
  Lemma time_sum_bound : forall (A : Type) (xs : list A) (f : A -> N) (w : A -> nat) c,
    (forall x, In x xs -> (f x <= c * N.of_nat (w x))%N) ->
    (fold_right N.add 0%N (map f xs) <= c * N.of_nat (sum_weight w xs))%N.
  Proof.
    intros A xs. induction xs as [|x xs IH]; intros f w c Hbound.
    - change (0 <= c * 0)%N. nia.
    - assert (Hx : (f x <= c * N.of_nat (w x))%N) by (apply Hbound; now left).
      assert (Hxs : (fold_right N.add 0%N (map f xs) <=
        c * N.of_nat (sum_weight w xs))%N).
      { apply IH. intros y Hin. apply Hbound. now right. }
      change (f x + fold_right N.add 0%N (map f xs) <=
        c * N.of_nat (w x + sum_weight w xs))%N.
      rewrite Nat2N.inj_add. nia.
  Qed.

  (** Sparse callback sums separate skeleton work from the payload weights they visit. *)
  Lemma map_sum_time_bound : forall (A B : Type) (wa : A -> nat) (wb : B -> nat)
      (tf : option A -> option B -> N) (ma : M.t A) (mb : M.t B) c clock,
    (forall a b, (tf a b <= c * N.of_nat (option_weight wa a +
      option_weight wb b + 1))%N) ->
    (clock <= M.c_map * ((tf None None + 1) * N.of_nat (M.nodes ma + M.nodes mb + 1) +
      fold_right N.add 0%N
        (map (fun p => tf (M.find p ma) (M.find p mb)) (M.codes ma ++ M.codes mb))))%N ->
    (clock <= M.c_map * (c + 1) * 2 * N.of_nat (code_work wa ma + code_work wb mb + 1))%N.
  Proof.
    intros A B wa wb tf ma mb c clock Hbound Hclock.
    pose proof (Hbound None None) as Hempty.
    change (tf None None <= c * 1)%N in Hempty. rewrite N.mul_1_r in Hempty.
    assert (Hsum : (fold_right N.add 0%N
        (map (fun p => tf (M.find p ma) (M.find p mb)) (M.codes ma ++ M.codes mb)) <=
      c * N.of_nat (sum_weight (fun p => (option_weight wa (M.find p ma) +
        option_weight wb (M.find p mb) + 1)%nat) (M.codes ma ++ M.codes mb)))%N).
    { apply time_sum_bound. intros p _. apply Hbound. }
    pose proof (pair_stored_weight_bound A B wa wb ma mb) as Hweight.
    assert (Hsum' : (fold_right N.add 0%N
        (map (fun p => tf (M.find p ma) (M.find p mb)) (M.codes ma ++ M.codes mb)) <=
      c * N.of_nat (2 * stored_weight wa ma + 2 * stored_weight wb mb +
        length (M.codes ma) + length (M.codes mb)))%N).
    { eapply N.le_trans; [exact Hsum|]. apply N.mul_le_mono_l. lia. }
    eapply N.le_trans; [exact Hclock|].
    replace (M.c_map * (c + 1) * 2 * N.of_nat (code_work wa ma + code_work wb mb + 1))%N
      with (M.c_map * (2 * (c + 1) *
        N.of_nat (code_work wa ma + code_work wb mb + 1)))%N by ring.
    apply N.mul_le_mono_l. clear Hclock Hsum Hbound Hweight.
    unfold code_work. rewrite !Nat2N.inj_add, !Nat2N.inj_mul in *. nia.
  Qed.

  (** The map merge clock is bounded by each input's own code work. *)
  Lemma T_merge_code_work : forall (A B C : Type)
      (f : option A -> option B -> option C) tf (wa : A -> nat) (wb : B -> nat) ma mb c,
    (forall a b, (tf a b <= c * N.of_nat (option_weight wa a +
      option_weight wb b + 1))%N) ->
    (M.T_merge f tf ma mb <= M.c_map * (c + 1) * 2 *
      N.of_nat (code_work wa ma + code_work wb mb + 1))%N.
  Proof.
    intros A B C f tf wa wb ma mb c Hbound. eapply map_sum_time_bound;
      [exact Hbound|apply M.T_merge_sum_le].
  Qed.

  (** Relational scanning has the same sparse code-work bound as merging. *)
  Lemma T_forall2b_code_work : forall (A B : Type)
      (f : option A -> option B -> bool) tf (wa : A -> nat) (wb : B -> nat) ma mb c,
    (forall a b, (tf a b <= c * N.of_nat (option_weight wa a +
      option_weight wb b + 1))%N) ->
    (M.T_forall2b f tf ma mb <= M.c_map * (c + 1) * 2 *
      N.of_nat (code_work wa ma + code_work wb mb + 1))%N.
  Proof.
    intros A B f tf wa wb ma mb c Hbound. eapply map_sum_time_bound;
      [exact Hbound|apply M.T_forall2b_sum_le].
  Qed.

  (** A bound comparison pays only for its present integer operands. *)
  Lemma T_bound_leb_le : forall a b,
    (T_bound_leb a b <= 8 * N.of_nat
      (option_weight Z.size_nat a + option_weight Z.size_nat b + 1))%N.
  Proof.
    intros [x|] [y|]; unfold option_weight; time_step.
  Qed.

  (** A bound join pays only for its present integer operands. *)
  Lemma T_bound_join_le : forall a b,
    (T_bound_join a b <= 8 * N.of_nat
      (option_weight Z.size_nat a + option_weight Z.size_nat b + 1))%N.
  Proof.
    intros [x|] [y|]; unfold option_weight; time_step.
  Qed.

  (** A bound meet pays only for its present integer operands. *)
  Lemma T_bound_meet_le : forall a b,
    (T_bound_meet a b <= 8 * N.of_nat
      (option_weight Z.size_nat a + option_weight Z.size_nat b + 1))%N.
  Proof.
    intros [x|] [y|]; unfold option_weight; time_step.
  Qed.

  (** A bound widening pays only for its present integer operands. *)
  Lemma T_bound_widen_le : forall a b,
    (T_bound_widen a b <= 8 * N.of_nat
      (option_weight Z.size_nat a + option_weight Z.size_nat b + 1))%N.
  Proof.
    intros [x|] [y|]; unfold option_weight; time_step.
  Qed.
  (** Empty maps enumerate no stored code. *)
  Lemma codes_empty : forall A, M.codes (@M.empty A) = nil.
  Proof.
    intro A. destruct (M.codes (@M.empty A)) as [|p ps] eqn:Hcodes; [reflexivity|].
    exfalso. assert (Hp : In p (M.codes (@M.empty A))).
    { rewrite Hcodes. now left. }
    apply M.codes_spec in Hp. rewrite M.find_empty in Hp. contradiction.
  Qed.

  (** Empty maps carry no payload weight. *)
  Lemma stored_weight_empty : forall (A : Type) (w : A -> nat),
    stored_weight w M.empty = 0.
  Proof.
    intros A w. unfold stored_weight. rewrite codes_empty. reflexivity.
  Qed.

  (** Empty maps contribute no skeleton, binding, or payload work. *)
  Lemma code_work_empty : forall (A : Type) (w : A -> nat), code_work w M.empty = 0.
  Proof.
    intros A w. unfold code_work. rewrite M.nodes_empty, codes_empty, stored_weight_empty.
    reflexivity.
  Qed.

  (** Replacing a missing row by the empty map preserves its zero work contribution. *)
  Lemma code_work_row_of : forall r,
    code_work Z.size_nat (row_of r) = option_weight (code_work Z.size_nat) r.
  Proof.
    intros [row|]; [reflexivity|apply code_work_empty].
  Qed.

  (** A common coefficient covers scalar work and one sparse row traversal. *)
  Definition row_time_factor : N := (32 * (M.c_map + 1))%N.

  (** Row comparison charges the two rows' own finite entries. *)
  Lemma T_row_leb_le : forall a b,
    (T_row_leb a b <= row_time_factor * N.of_nat
      (option_weight (code_work Z.size_nat) a +
       option_weight (code_work Z.size_nat) b + 1))%N.
  Proof.
    intros a b.
    assert (Hwork : (1 <= N.of_nat (option_weight (code_work Z.size_nat) a +
      option_weight (code_work Z.size_nat) b + 1))%N) by lia.
    pose proof (T_forall2b_code_work Z Z bound_leb (fun x y => T_bound_leb x y)
      Z.size_nat Z.size_nat
      (row_of a) (row_of b) 8%N T_bound_leb_le) as Hscan.
    rewrite !code_work_row_of in Hscan. unfold row_time_factor. time_step.
  Qed.

  (** Row join charges the two rows' own finite entries. *)
  Lemma T_row_join_le : forall a b,
    (T_row_join a b <= row_time_factor * N.of_nat
      (option_weight (code_work Z.size_nat) a +
       option_weight (code_work Z.size_nat) b + 1))%N.
  Proof.
    intros a b.
    assert (Hwork : (1 <= N.of_nat (option_weight (code_work Z.size_nat) a +
      option_weight (code_work Z.size_nat) b + 1))%N) by lia.
    destruct a as [ra|], b as [rb|].
    - pose proof (T_merge_code_work Z Z Z bound_join (fun x y => T_bound_join x y)
        Z.size_nat Z.size_nat
        ra rb 8%N T_bound_join_le) as Hmerge. unfold row_time_factor. time_step.
    - unfold row_time_factor. time_step.
    - unfold row_time_factor. time_step.
    - unfold row_time_factor. time_step.
  Qed.

  (** Row meet charges the two rows' own finite entries. *)
  Lemma T_row_meet_le : forall a b,
    (T_row_meet a b <= row_time_factor * N.of_nat
      (option_weight (code_work Z.size_nat) a +
       option_weight (code_work Z.size_nat) b + 1))%N.
  Proof.
    intros a b.
    assert (Hwork : (1 <= N.of_nat (option_weight (code_work Z.size_nat) a +
      option_weight (code_work Z.size_nat) b + 1))%N) by lia.
    destruct a as [ra|], b as [rb|].
    - pose proof (T_merge_code_work Z Z Z bound_meet (fun x y => T_bound_meet x y)
        Z.size_nat Z.size_nat
        ra rb 8%N T_bound_meet_le) as Hmerge. unfold row_time_factor. time_step.
    - unfold row_time_factor. time_step.
    - unfold row_time_factor. time_step.
    - unfold row_time_factor. time_step.
  Qed.

  (** Row widening charges the two rows' own finite entries. *)
  Lemma T_row_widen_le : forall a b,
    (T_row_widen a b <= row_time_factor * N.of_nat
      (option_weight (code_work Z.size_nat) a +
       option_weight (code_work Z.size_nat) b + 1))%N.
  Proof.
    intros a b.
    assert (Hwork : (1 <= N.of_nat (option_weight (code_work Z.size_nat) a +
      option_weight (code_work Z.size_nat) b + 1))%N) by lia.
    destruct a as [ra|].
    - pose proof (T_merge_code_work Z Z Z bound_widen (fun x y => T_bound_widen x y)
        Z.size_nat Z.size_nat
        ra (row_of b) 8%N T_bound_widen_le) as Hmerge.
      rewrite code_work_row_of in Hmerge. unfold row_time_factor. time_step.
    - unfold row_time_factor. time_step.
  Qed.

  (** Pointwise weight bounds lift to their list sums. *)
  Lemma sum_weight_mono : forall (A : Type) (f g : A -> nat) xs,
    (forall x, In x xs -> f x <= g x) -> sum_weight f xs <= sum_weight g xs.
  Proof.
    intros A f g xs. induction xs as [|x xs IH]; intro Hbound; [reflexivity|].
    assert (Hx : f x <= g x) by (apply Hbound; now left).
    assert (Hxs : sum_weight f xs <= sum_weight g xs).
    { apply IH. intros y Hin. apply Hbound. now right. }
    change (f x + sum_weight f xs <= g x + sum_weight g xs). lia.
  Qed.

  (** Constant weights multiply the list length. *)
  Lemma sum_weight_const : forall (A : Type) (xs : list A) n,
    sum_weight (fun _ => n) xs = length xs * n.
  Proof.
    intros A xs. induction xs as [|x xs IH]; intro n; [reflexivity|].
    change (n + sum_weight (fun _ : A => n) xs = S (length xs) * n).
    rewrite IH. lia.
  Qed.

  (** Summing outer payloads agrees with summing the collected rows. *)
  Lemma stored_weight_rows : forall (w : M.t Z -> nat) m,
    stored_weight w m = sum_weight w (rows m).
  Proof.
    intros w m. unfold stored_weight, sum_weight, rows.
    induction (M.codes m) as [|p ps IH]; [reflexivity|].
    cbn [map fold_right flat_map]. destruct (M.find p m) eqn:Hrow;
      cbn [option_weight map fold_right app]; now rewrite IH.
  Qed.

  (** Each collected row's finite-entry bits are bounded by the matrix maximum. *)
  Lemma stored_row_bits_bound : forall m p row,
    M.find p m = Some row -> stored_weight Z.size_nat row <=
      length (M.codes row) * ell m.
  Proof.
    intros m p row Hrow. unfold stored_weight, sum_weight. apply sum_members_bound.
    intros q Hq. destruct (M.find q row) as [z|] eqn:Hentry.
    - change (Z.size_nat z <= ell m). apply (ell_entry m p q z).
      unfold raw_entry. rewrite Hrow. exact Hentry.
    - change (0 <= ell m). lia.
  Qed.

  (** A collected row pays for its skeleton and at most one entry per supported code. *)
  Lemma row_code_work_bound : forall m row, In row (rows m) ->
    code_work Z.size_nat row <= M.nodes row + supp m * (ell m + 1).
  Proof.
    intros m row Hin.
    assert (Hsupport : forall q, In q (M.codes row) -> In q (support m)).
    { intros q Hq. apply support_spec. right. apply in_flat_map. exists row. now split. }
    pose proof (codes_support_length Z row m Hsupport) as Hlength.
    apply rows_find in Hin. destruct Hin as [p Hrow].
    pose proof (stored_row_bits_bound m p row Hrow) as Hbits.
    unfold code_work. nia.
  Qed.

  (** The public quadratic size covers raw code work and the complete sparse skeleton. *)
  Lemma matrix_code_work_le : forall m,
    code_work (code_work Z.size_nat) m <= size (Reached m).
  Proof.
    intro m.
    assert (Houter : length (M.codes m) <= supp m).
    { apply codes_support_length. intros p Hp. apply support_spec. now left. }
    pose proof (rows_length m) as Hrows.
    assert (Hsum : sum_weight (code_work Z.size_nat) (rows m) <=
      sum_weight (fun row => M.nodes row + supp m * (ell m + 1)) (rows m)).
    { apply sum_weight_mono. intros row Hin. now apply row_code_work_bound. }
    rewrite sum_weight_add, sum_weight_const in Hsum.
    change (sum_weight (code_work Z.size_nat) (rows m) <=
      sum_weight M.nodes (rows m) + length (rows m) * (supp m * (ell m + 1))) in Hsum.
    assert (Hprod : length (rows m) * (supp m * (ell m + 1)) <=
      supp m * (supp m * (ell m + 1))).
    { apply Nat.mul_le_mono_r. lia. }
    unfold code_work at 1. rewrite stored_weight_rows.
    change (M.nodes m + length (M.codes m) + sum_weight (code_work Z.size_nat) (rows m) <=
      (supp m + 1)^2 * (b m + ell m + 1) +
      (M.nodes m + sum_weight M.nodes (rows m))). cbn [Nat.pow]. nia.
  Qed.

  (** The sparse skeleton and stored codes cover all finite-entry bit work. *)
  Lemma code_work_entries : forall m,
    code_work (code_work Z.size_nat) m <=
      (skel m + entries (Reached m)) * (ell m + 1).
  Proof.
    intro m.
    assert (Hsum : sum_weight (code_work Z.size_nat) (rows m) <=
      sum_weight (fun row => M.nodes row + length (M.codes row) * (ell m + 1)) (rows m)).
    { apply sum_weight_mono. intros row Hin.
      apply rows_find in Hin. destruct Hin as [p Hrow].
      pose proof (stored_row_bits_bound m p row Hrow) as Hbits.
      unfold code_work. nia. }
    assert (Hscale : forall rs : list (M.t Z),
      sum_weight (fun row => length (M.codes row) * (ell m + 1)) rs =
      sum_weight (fun row => length (M.codes row)) rs * (ell m + 1)).
    { intro rs. induction rs as [|row rs IH]; [reflexivity|].
      change (length (M.codes row) * (ell m + 1) +
        sum_weight (fun r => length (M.codes r) * (ell m + 1)) rs =
        (length (M.codes row) + sum_weight (fun r => length (M.codes r)) rs) * (ell m + 1)).
      rewrite IH. ring. }
    rewrite sum_weight_add, Hscale in Hsum.
    unfold code_work at 1. rewrite stored_weight_rows.
    change (M.nodes m + length (M.codes m) + sum_weight (code_work Z.size_nat) (rows m) <=
      (M.nodes m + sum_weight M.nodes (rows m) +
        (length (M.codes m) + sum_weight (fun row => length (M.codes row)) (rows m))) *
      (ell m + 1)). nia.
  Qed.

  (** Lattice operations charge sparse structure, stored codes, labels, and entry bits. *)
  Definition lattice_work (a b : t) : nat :=
    (skels a + skels b + entries a + entries b + labs a + labs b + 1) *
      (bs a + bs b + ells a + ells b + 1).

  (** The sparse lattice budget also covers constant dispatch on empty states. *)
  Lemma lattice_work_pos : forall a b, 1 <= lattice_work a b.
  Proof.
    intros a b. unfold lattice_work. nia.
  Qed.

  (** The two arguments contribute symmetrically to the lattice budget. *)
  Lemma lattice_work_sym : forall a b, lattice_work a b = lattice_work b a.
  Proof.
    intros a b. unfold lattice_work. ring.
  Qed.

  (** The published sparse lattice budget covers both matrices' nested code work. *)
  Lemma matrix_code_work_lattice : forall ma mb,
    code_work (code_work Z.size_nat) ma + code_work (code_work Z.size_nat) mb + 1 <=
      lattice_work (Reached ma) (Reached mb).
  Proof.
    intros ma mb. pose proof (code_work_entries ma) as Ha.
    pose proof (code_work_entries mb) as Hb.
    unfold lattice_work, skels, labs, bs, ells. nia.
  Qed.

  (** A matrix traversal adds one outer sparse-map pass to the row bound. *)
  Definition matrix_time_factor : N := (M.c_map * (row_time_factor + 1) * 2 + 8)%N.

  (** Comparing two reached matrices is linear in their nested code work. *)
  Lemma T_leb_matrix_le : forall ma mb,
    (T_leb (Reached ma) (Reached mb) <= matrix_time_factor * N.of_nat
      (code_work (code_work Z.size_nat) ma + code_work (code_work Z.size_nat) mb + 1))%N.
  Proof.
    intros ma mb.
    assert (Hwork : (1 <= N.of_nat (code_work (code_work Z.size_nat) ma +
      code_work (code_work Z.size_nat) mb + 1))%N) by lia.
    pose proof (T_forall2b_code_work (M.t Z) (M.t Z) row_leb (fun x y => T_row_leb x y)
      (code_work Z.size_nat) (code_work Z.size_nat) ma mb row_time_factor T_row_leb_le)
      as Hscan. unfold matrix_time_factor. time_step.
  Qed.

  (** Joining two reached matrices is linear in their nested code work. *)
  Lemma T_join_matrix_le : forall ma mb,
    (T_join (Reached ma) (Reached mb) <= matrix_time_factor * N.of_nat
      (code_work (code_work Z.size_nat) ma + code_work (code_work Z.size_nat) mb + 1))%N.
  Proof.
    intros ma mb.
    assert (Hwork : (1 <= N.of_nat (code_work (code_work Z.size_nat) ma +
      code_work (code_work Z.size_nat) mb + 1))%N) by lia.
    pose proof (T_merge_code_work (M.t Z) (M.t Z) (M.t Z) row_join (fun x y => T_row_join x y)
      (code_work Z.size_nat) (code_work Z.size_nat) ma mb row_time_factor T_row_join_le)
      as Hmerge. unfold matrix_time_factor. time_step.
  Qed.

  (** Meeting two reached matrices is linear in their nested code work. *)
  Lemma T_meet_matrix_le : forall ma mb,
    (T_meet (Reached ma) (Reached mb) <= matrix_time_factor * N.of_nat
      (code_work (code_work Z.size_nat) ma + code_work (code_work Z.size_nat) mb + 1))%N.
  Proof.
    intros ma mb.
    assert (Hwork : (1 <= N.of_nat (code_work (code_work Z.size_nat) ma +
      code_work (code_work Z.size_nat) mb + 1))%N) by lia.
    pose proof (T_merge_code_work (M.t Z) (M.t Z) (M.t Z) row_meet (fun x y => T_row_meet x y)
      (code_work Z.size_nat) (code_work Z.size_nat) ma mb row_time_factor T_row_meet_le)
      as Hmerge. unfold matrix_time_factor. time_step.
  Qed.

  (** The widening update itself is linear in its two input matrices' code work. *)
  Lemma T_widen_merge_le : forall ma mb,
    (M.T_merge row_widen (fun x y => T_row_widen x y) ma mb <= matrix_time_factor * N.of_nat
      (code_work (code_work Z.size_nat) ma + code_work (code_work Z.size_nat) mb + 1))%N.
  Proof.
    intros ma mb.
    pose proof (T_merge_code_work (M.t Z) (M.t Z) (M.t Z) row_widen (fun x y => T_row_widen x y)
      (code_work Z.size_nat) (code_work Z.size_nat) ma mb row_time_factor T_row_widen_le)
      as Hmerge. unfold matrix_time_factor. nia.
  Qed.

  (** A matrix pass has a positive coefficient even when the map clock is zero. *)
  Lemma matrix_time_factor_pos : (1 <= matrix_time_factor)%N.
  Proof.
    unfold matrix_time_factor. nia.
  Qed.

  (** The lattice coefficient covers both widening passes and constant dispatch work. *)
  Lemma matrix_time_factor_lat : (2 * matrix_time_factor + 8 <= c_lat)%N.
  Proof.
    unfold matrix_time_factor, row_time_factor, c_lat. nia.
  Qed.

  (** Inclusion scans the sparse matrices within the entry-based lattice budget. *)
  Lemma T_leb_entries_le : forall a b,
    (T_leb a b <= matrix_time_factor * N.of_nat (lattice_work a b))%N.
  Proof.
    intros a b.
    assert (Hfactor : (8 <= matrix_time_factor)%N) by (unfold matrix_time_factor; nia).
    assert (Hwork : (1 <= N.of_nat (lattice_work a b))%N).
    { pose proof (lattice_work_pos a b). lia. }
    destruct a as [|ma], b as [|mb].
    - time_step.
    - time_step.
    - time_step.
    - eapply N.le_trans; [apply T_leb_matrix_le|].
      apply N.mul_le_mono_l, time_of_nat_le, matrix_code_work_lattice.
  Qed.

  (** Join merges the sparse matrices within the entry-based lattice budget. *)
  Lemma T_join_entries_le : forall a b,
    (T_join a b <= matrix_time_factor * N.of_nat (lattice_work a b))%N.
  Proof.
    intros a b.
    assert (Hfactor : (8 <= matrix_time_factor)%N) by (unfold matrix_time_factor; nia).
    assert (Hwork : (1 <= N.of_nat (lattice_work a b))%N).
    { pose proof (lattice_work_pos a b). lia. }
    destruct a as [|ma], b as [|mb].
    - time_step.
    - time_step.
    - time_step.
    - eapply N.le_trans; [apply T_join_matrix_le|].
      apply N.mul_le_mono_l, time_of_nat_le, matrix_code_work_lattice.
  Qed.

  (** Widening pays for one comparison and at most one sparse merge. *)
  Lemma T_widen_entries_le : forall p a b,
    (T_widen p a b <= c_lat * N.of_nat (lattice_work a b))%N.
  Proof.
    intros p a b. pose proof (T_leb_entries_le b a) as Hcompare.
    rewrite (lattice_work_sym b a) in Hcompare.
    set (work := N.of_nat (lattice_work a b)) in *.
    assert (Hwork : (1 <= work)%N).
    { unfold work. pose proof (lattice_work_pos a b). lia. }
    assert (Hmerge : forall ma mb, a = Reached ma -> b = Reached mb ->
      (M.T_merge row_widen (fun x y => T_row_widen x y) ma mb <=
        matrix_time_factor * work)%N).
    { intros ma mb Ha Hb. subst a b. unfold work.
      eapply N.le_trans; [apply T_widen_merge_le|].
      apply N.mul_le_mono_l, time_of_nat_le, matrix_code_work_lattice. }
    assert (Hbudget : ((2 * matrix_time_factor + 8) * work <= c_lat * work)%N).
    { apply N.mul_le_mono_r. exact matrix_time_factor_lat. }
    clearbody work. unfold T_widen. cbn beta iota zeta.
    destruct (leb b a); cbn beta iota zeta.
    - nia.
    - destruct a as [|ma], b as [|mb]; cbn beta iota zeta.
      + nia.
      + nia.
      + nia.
      + specialize (Hmerge ma mb eq_refl eq_refl). nia.
  Qed.

  (** Comparison dispatch and sparse scanning fit the matrix coefficient. *)
  Lemma T_leb_base_le : forall a b,
    (T_leb a b <= matrix_time_factor * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros [|ma] [|mb].
    - pose proof matrix_time_factor_pos. time_step.
    - pose proof matrix_time_factor_pos. time_step.
    - pose proof matrix_time_factor_pos. time_step.
    - eapply N.le_trans; [apply T_leb_matrix_le|]. apply N.mul_le_mono_l.
      apply time_of_nat_le, Nat.add_le_mono_r, Nat.add_le_mono;
        apply matrix_code_work_le.
  Qed.

  (** Join dispatch and sparse merging fit the matrix coefficient. *)
  Lemma T_join_base_le : forall a b,
    (T_join a b <= matrix_time_factor * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros [|ma] [|mb].
    - pose proof matrix_time_factor_pos. time_step.
    - pose proof matrix_time_factor_pos. time_step.
    - pose proof matrix_time_factor_pos. time_step.
    - eapply N.le_trans; [apply T_join_matrix_le|]. apply N.mul_le_mono_l.
      apply time_of_nat_le, Nat.add_le_mono_r, Nat.add_le_mono;
        apply matrix_code_work_le.
  Qed.

  (** Meet dispatch and sparse merging fit the matrix coefficient. *)
  Lemma T_meet_base_le : forall a b,
    (T_meet a b <= matrix_time_factor * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros [|ma] [|mb].
    - pose proof matrix_time_factor_pos. time_step.
    - pose proof matrix_time_factor_pos. time_step.
    - pose proof matrix_time_factor_pos. time_step.
    - eapply N.le_trans; [apply T_meet_matrix_le|]. apply N.mul_le_mono_l.
      apply time_of_nat_le, Nat.add_le_mono_r, Nat.add_le_mono;
        apply matrix_code_work_le.
  Qed.

  (** The widening merge is bounded by the public sizes of its two matrices. *)
  Lemma T_widen_merge_size : forall ma mb,
    (M.T_merge row_widen (fun x y => T_row_widen x y) ma mb <= matrix_time_factor *
      N.of_nat (size (Reached ma) + size (Reached mb) + 1))%N.
  Proof.
    intros ma mb. eapply N.le_trans; [apply T_widen_merge_le|].
    apply N.mul_le_mono_l.
    apply time_of_nat_le, Nat.add_le_mono_r, Nat.add_le_mono;
      apply matrix_code_work_le.
  Qed.

  (** The public inclusion clock is linear in the two raw matrix sizes. *)
  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. eapply N.le_trans; [apply T_leb_base_le|]. apply N.mul_le_mono_r.
    pose proof matrix_time_factor_lat. lia.
  Qed.

  (** The public join clock is linear in the two raw matrix sizes. *)
  Lemma T_join_le : forall a b,
    (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. eapply N.le_trans; [apply T_join_base_le|]. apply N.mul_le_mono_r.
    pose proof matrix_time_factor_lat. lia.
  Qed.

  (** Bottom recognition takes constant work within the lattice size bound. *)
  Lemma T_is_bot_le : forall s,
    (T_is_bot s <= c_lat * N.of_nat (size s + 1))%N.
  Proof.
    intro s. assert (Hclock : (T_is_bot s <= 1)%N).
    { destruct s; time_step. }
    eapply N.le_trans; [exact Hclock|].
    change (1 * 1 <= c_lat * N.of_nat (size s + 1))%N.
    apply N.mul_le_mono; [exact c_lat_pos|lia].
  Qed.

  (** Widening pays for one inclusion check and at most one sparse merge. *)
  Lemma T_widen_le : forall p a b,
    (T_widen p a b <= c_lat * N.of_nat
      ((wunits a + wunits b) * wsize p + (size a + size b + wsize p + 1)))%N.
  Proof.
    intros p a b. unfold wsize.
    rewrite Nat.mul_0_r, Nat.add_0_l, Nat.add_0_r.
    pose proof (T_leb_base_le b a) as Hcompare.
    replace (size b + size a + 1) with (size a + size b + 1) in Hcompare by lia.
    set (work := N.of_nat (size a + size b + 1)) in *.
    assert (Hwork : (1 <= work)%N) by (unfold work; lia).
    assert (Hmerge : forall ma mb, a = Reached ma -> b = Reached mb ->
      (M.T_merge row_widen (fun x y => T_row_widen x y) ma mb <=
        matrix_time_factor * work)%N).
    { intros ma mb Ha Hb. subst a b. unfold work. apply T_widen_merge_size. }
    assert (Hbudget : ((2 * matrix_time_factor + 8) * work <= c_lat * work)%N).
    { apply N.mul_le_mono_r. exact matrix_time_factor_lat. }
    clearbody work. unfold T_widen. cbn beta iota zeta.
    destruct (leb b a); cbn beta iota zeta.
    - nia.
    - destruct a as [|ma], b as [|mb]; cbn beta iota zeta.
      + nia.
      + nia.
      + nia.
      + specialize (Hmerge ma mb eq_refl eq_refl). nia.
  Qed.

  (** Narrowing uses the meet clock within the common lattice size bound. *)
  Lemma T_narrow_le : forall a b,
    (T_narrow a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros a b. pose proof (T_meet_base_le a b) as Hmeet.
    set (work := N.of_nat (size a + size b + 1)) in *.
    assert (Hwork : (1 <= work)%N) by (unfold work; lia).
    assert (Hbudget : ((2 * matrix_time_factor + 8) * work <= c_lat * work)%N).
    { apply N.mul_le_mono_r. exact matrix_time_factor_lat. }
    clearbody work. unfold T_narrow. cbn beta iota zeta. nia.
  Qed.
  (** Optional zero weights vanish independently of presence. *)
  Lemma option_weight_zero : forall (A : Type) (a : option A),
    option_weight (fun _ => 0) a = 0.
  Proof.
    intros A [a|]; reflexivity.
  Qed.

  (** Stored payload weights inherit a bound established at each successful lookup. *)
  Lemma stored_weight_uniform : forall (A : Type) (w : A -> nat) (m : M.t A) upper,
    (forall p a, M.find p m = Some a -> w a <= upper) ->
    stored_weight w m <= length (M.codes m) * upper.
  Proof.
    intros A w m upper Hbound. unfold stored_weight, sum_weight. apply sum_members_bound.
    intros p Hp. destruct (M.find p m) as [a|] eqn:Ha.
    - change (w a <= upper). exact (Hbound p a Ha).
    - change (0 <= upper). lia.
  Qed.

  (** Zero payload weights leave only skeleton and binding work. *)
  Lemma code_work_zero : forall (A : Type) (m : M.t A),
    code_work (fun _ => 0) m = M.nodes m + length (M.codes m).
  Proof.
    intros A m.
    assert (Hweight : stored_weight (fun _ : A => 0) m <= length (M.codes m) * 0).
    { apply stored_weight_uniform. intros p a Ha. lia. }
    unfold code_work. nia.
  Qed.

  (** A retrieved row uses only the matrix's supported codes. *)
  Lemma row_lookup_support : forall m k p,
    In p (M.codes (row_of (M.get k m))) -> In p (support m).
  Proof.
    intros m k p Hp. apply M.codes_spec in Hp. apply support_find. right.
    exists (K.encode k). unfold raw_entry. now rewrite <- M.get_find.
  Qed.

  (** Each finite entry in a retrieved row satisfies the matrix bit bound. *)
  Lemma row_lookup_bits : forall m k p z,
    M.find p (row_of (M.get k m)) = Some z -> Z.size_nat z <= ell m.
  Proof.
    intros m k p z Hentry. apply (ell_entry m (K.encode k) p z).
    unfold raw_entry. now rewrite <- M.get_find.
  Qed.

  (** A supported row's shifted payload work is bounded by its support and bit maxima. *)
  Lemma code_work_bits_bound : forall m row shift upper,
    (forall p, In p (M.codes row) -> In p (support m)) ->
    (forall p z, M.find p row = Some z -> Z.size_nat z <= upper) ->
    code_work (fun z => shift + Z.size_nat z + 1) row <=
      supp m * (b m + upper + shift + 3).
  Proof.
    intros m row shift upper Hsupport Hbits.
    pose proof (nodes_support Z row m Hsupport) as Hnodes.
    pose proof (codes_support_length Z row m Hsupport) as Hcount.
    assert (Hweight : stored_weight (fun z => shift + Z.size_nat z + 1) row <=
      length (M.codes row) * (shift + upper + 1)).
    { apply stored_weight_uniform. intros p z Hentry.
      pose proof (Hbits p z Hentry). lia. }
    unfold code_work. nia.
  Qed.

  (** Sum bit length is bounded by the two operand bit lengths and one carry bit. *)
  Lemma zbits_add_sum : forall a d,
    Z.size_nat (a + d)%Z <= Z.size_nat a + Z.size_nat d + 1.
  Proof.
    intros a d. apply zbits_add_bound; lia.
  Qed.

  (** Forgetting both signed columns charges two key removals at each present row. *)
  Lemma T_forget_row_le : forall x a b,
    (T_forget_row x a b <= 16 * (M.c_map + 1) * N.of_nat
      (option_weight (fun _ : M.t Z => (X.bits x + 1)%nat) a + 1))%N.
  Proof.
    intros x [row|] ignored; cbn [option_weight].
    - pose proof (M.T_remove_le Z (x, false) row) as Hnegative.
      pose proof (M.T_remove_le Z (x, true) (M.remove (x, false) row)) as Hpositive.
      rewrite !literal_bits in *. cbn beta iota zeta in Hnegative, Hpositive.
      unfold T_forget_row. cbn beta iota zeta.
      rewrite ?Nat2N.inj_add, ?Nat2N.inj_mul in *. nia.
    - unfold T_forget_row. cbn beta iota zeta. nia.
  Qed.

  (** Removing signed outer bindings leaves only codes from the original support. *)
  Lemma removed_signed_codes_support : forall m x p,
    In p (M.codes (M.remove (x, true) (M.remove (x, false) m))) ->
    In p (support m).
  Proof.
    intros m x p Hp. apply M.codes_spec in Hp. rewrite !M.find_remove in Hp.
    destruct (Pos.eqb p (K.encode (x, true))),
      (Pos.eqb p (K.encode (x, false))); try contradiction.
    apply support_spec. left. now apply M.codes_spec.
  Qed.

  Lemma havoc_code_work_bound : forall m x,
    code_work (fun _ : M.t Z => (X.bits x + 1)%nat)
      (M.remove (x, true) (M.remove (x, false) m)) <=
    supp m * (b m + X.bits x + 3).
  Proof.
    intros m x.
    pose proof (codes_support_length (M.t Z)
      (M.remove (x, true) (M.remove (x, false) m)) m
      (removed_signed_codes_support m x)) as Hcount.
    pose proof (nodes_support (M.t Z)
      (M.remove (x, true) (M.remove (x, false) m)) m
      (removed_signed_codes_support m x)) as Hnodes.
    pose proof (stored_weight_uniform (M.t Z)
      (fun _ : M.t Z => (X.bits x + 1)%nat)
      (M.remove (x, true) (M.remove (x, false) m))
      (X.bits x + 1) ltac:(intros; apply Nat.le_refl)) as Hweight.
    unfold code_work. nia.
  Qed.

  (** Signed havoc has a quadratic map coefficient and linear raw support work. *)
  Lemma T_havoc_small : forall x m,
    (T_havoc x (Reached m) <= 128 * (M.c_map + 1) * (M.c_map + 1) *
      N.of_nat ((supp m + 1) * (b m + X.bits x + 4) + 1))%N.
  Proof.
    intros x m.
    assert (Hcallback : forall a b,
      (T_forget_row x a b <= 16 * (M.c_map + 1) * N.of_nat
        (option_weight (fun _ : M.t Z => (X.bits x + 1)%nat) a +
          option_weight (fun _ : M.t Z => 0%nat) b + 1))%N).
    { intros a b. rewrite option_weight_zero, Nat.add_0_r. apply T_forget_row_le. }
    pose proof (T_merge_code_work (M.t Z) (M.t Z) (M.t Z) (forget_row x)
      (fun a b => T_forget_row x a b)
      (fun _ : M.t Z => (X.bits x + 1)%nat) (fun _ : M.t Z => 0)
      (M.remove (x, true) (M.remove (x, false) m)) M.empty
      (16 * (M.c_map + 1))%N Hcallback) as Hmerge.
    rewrite code_work_empty in Hmerge.
    pose proof (havoc_code_work_bound m x) as Hwork.
    set (work := N.of_nat ((supp m + 1) * (b m + X.bits x + 4) + 1)).
    assert (Hpositive : (1 <= work)%N) by (unfold work; lia).
    assert (Hmerge' : (M.T_merge (forget_row x)
      (fun a b => T_forget_row x a b)
      (M.remove (x, true) (M.remove (x, false) m)) M.empty <=
      M.c_map * (16 * (M.c_map + 1) + 1) * 2 * work)%N).
    { eapply N.le_trans; [exact Hmerge|].
      apply N.mul_le_mono_l. unfold work. apply time_of_nat_le. nia. }
    assert (Hremove : forall sign (n : dbm),
      (M.T_remove (x, sign) n <= 2 * M.c_map * work)%N).
    { intros sign n. eapply N.le_trans; [apply M.T_remove_le|].
      replace (2 * M.c_map * work)%N with (M.c_map * (2 * work))%N by ring.
      apply N.mul_le_mono_l. pose proof (signed_bits_le x sign). unfold work. lia. }
    pose proof (Hremove false m) as Hnegative.
    pose proof (Hremove true (M.remove (x, false) m)) as Hpositive_key.
    assert (Hsum : (1 + (M.T_remove (x, false) m +
      M.T_remove (x, true) (M.remove (x, false) m) +
      M.T_merge (forget_row x) (fun a b => T_forget_row x a b)
        (M.remove (x, true) (M.remove (x, false) m)) M.empty) <=
      (1 + 4 * M.c_map + M.c_map * (16 * (M.c_map + 1) + 1) * 2) * work)%N).
    { rewrite !N.mul_add_distr_r. rewrite N.mul_1_l. lia. }
    assert (Hcoefficient : (1 + 4 * M.c_map +
      M.c_map * (16 * (M.c_map + 1) + 1) * 2 <=
      128 * (M.c_map + 1) * (M.c_map + 1))%N) by nia.
    unfold T_havoc. cbn beta iota zeta. clearbody work.
    clear - Hsum Hcoefficient.
    eapply N.le_trans; [|apply N.mul_le_mono_r; exact Hcoefficient].
    lia.
  Qed.

  Lemma T_havoc_le : forall x s,
    (T_havoc x s <= c_num * N.of_nat (havoc_work x s + 1))%N.
  Proof.
    intros x [|m].
    - assert (Hconstant : (1 <= c_num)%N) by (unfold c_num; nia).
      assert (Hwork : (1 <= N.of_nat (havoc_work x Unreached + 1))%N) by lia.
      unfold T_havoc. cbn beta iota zeta. nia.
    - pose proof (T_havoc_small x m) as Htime.
      assert (Hwork : (supp m + 1) * (b m + X.bits x + 4) + 1 <=
        4 * (havoc_work x (Reached m) + 1)).
      { unfold havoc_work, ns, bs, ells, skels. cbn [Nat.pow]. nia. }
      assert (Hcast : (N.of_nat ((supp m + 1) * (b m + X.bits x + 4) + 1) <=
        4 * N.of_nat (havoc_work x (Reached m) + 1))%N).
      { pose proof (time_of_nat_le _ _ Hwork) as Hcasted.
        rewrite Nat2N.inj_mul in Hcasted. exact Hcasted. }
      assert (Hcoefficient : (128 * (M.c_map + 1) * (M.c_map + 1) * 4 <= c_num)%N).
      { unfold c_num. nia. }
      eapply N.le_trans; [exact Htime|].
      eapply N.le_trans; [apply N.mul_le_mono_l; exact Hcast|].
      rewrite N.mul_assoc. apply N.mul_le_mono_r. exact Hcoefficient.
  Qed.


  Lemma T_column_present_small : forall k row,
    (T_column_present k row <= 4 * (M.c_map + 1) * N.of_nat (K.bits k + 1))%N.
  Proof.
    intros k row. time_step.
  Qed.

  (** An existential scan pays only for callbacks at stored payloads. *)
  Lemma T_existsb_code_work : forall (A : Type) (f : A -> bool) tf
      (w : A -> nat) (m : M.t A) c,
    (forall a, (tf a <= c * N.of_nat (w a))%N) ->
    (M.T_existsb f tf m <= M.c_map * (c + 1) * N.of_nat (code_work w m + 1))%N.
  Proof.
    intros A f tf w m c Hbound. pose proof (M.T_existsb_sum_le A f tf m) as Hclock.
    assert (Hsum : (fold_right N.add 0%N (map (fun p =>
      match M.find p m with Some a => tf a | None => 0%N end) (M.codes m)) <=
      c * N.of_nat (stored_weight w m))%N).
    { unfold stored_weight. apply time_sum_bound. intros p Hp.
      destruct (M.find p m) as [a|].
      - change (tf a <= c * N.of_nat (w a))%N. apply Hbound.
      - change (0 <= c * N.of_nat 0)%N. nia. }
    eapply N.le_trans; [exact Hclock|].
    replace (M.c_map * (c + 1) * N.of_nat (code_work w m + 1))%N with
      (M.c_map * ((c + 1) * N.of_nat (code_work w m + 1)))%N by ring.
    apply N.mul_le_mono_l. clear Hclock Hbound.
    unfold code_work. rewrite !Nat2N.inj_add in *. nia.
  Qed.

  (** Path relaxation charges prefix bits only when a finite suffix is processed. *)
  Lemma T_via_bound_le : forall a old next,
    (T_via_bound a old next <= 8 * N.of_nat
      (option_weight (fun z => (Z.size_nat a + Z.size_nat z + 1)%nat) next + 1))%N.
  Proof.
    intros a old [z|].
    - pose proof (zbits_add_sum a z) as Hsum. destruct old;
        unfold option_weight; time_step.
    - destruct old; unfold option_weight; time_step.
  Qed.

  (** A pivot row update pays for lookup, the source skeleton, and finite pivot payloads. *)
  Definition pivot_row_work (k : K.t) (pivot row : M.t Z) : nat :=
    K.bits k + 1 + code_work (fun _ : Z => 0) row +
      match M.get k row with
      | Some a => code_work (fun z => Z.size_nat a + Z.size_nat z + 1) pivot
      | None => 0
      end.

  Lemma T_round_row_le : forall k pivot a b,
    (T_round_row k pivot a b <= row_time_factor *
      N.of_nat (option_weight (pivot_row_work k pivot) a + 1))%N.
  Proof.
    intros k pivot [row|] ignored.
    - cbn [option_weight]. unfold pivot_row_work.
      destruct (M.get k row) as [a|] eqn:Ha.
      + assert (Hcallback : forall old next,
          (T_via_bound a old next <= 8 * N.of_nat
            (option_weight (fun _ : Z => 0%nat) old +
             option_weight (fun z => (Z.size_nat a + Z.size_nat z + 1)%nat) next + 1))%N).
        { intros old next. rewrite option_weight_zero. apply T_via_bound_le. }
        pose proof (T_merge_code_work Z Z Z (via_bound a)
          (fun x y => T_via_bound a x y) (fun _ : Z => 0)
          (fun z => Z.size_nat a + Z.size_nat z + 1) row pivot 8%N Hcallback) as Hmerge.
        pose proof (M.T_get_le Z k row) as Hget.
        set (lookup_bits := K.bits k + 1) in *.
        set (source_work := code_work (fun _ : Z => 0) row) in *.
        set (pivot_work := code_work (fun z => Z.size_nat a + Z.size_nat z + 1) pivot) in *.
        clearbody lookup_bits source_work pivot_work. clear Hcallback.
        unfold T_round_row, T_relax_row. cbn beta iota zeta. rewrite Ha. cbn beta iota zeta.
        set (get_clock := M.T_get k row) in *.
        set (merge_clock := M.T_merge (via_bound a)
          (fun x y => T_via_bound a x y) row pivot) in *.
        clearbody get_clock merge_clock. clear Ha.
        unfold row_time_factor.
        repeat rewrite Nat2N.inj_add in Hget.
        repeat rewrite Nat2N.inj_add in Hmerge.
        repeat rewrite Nat2N.inj_add.
        set (work := (N.of_nat lookup_bits + N.of_nat source_work +
          N.of_nat pivot_work + 1)%N).
        match goal with
        | |- N.le ?clock _ => change (clock <= 32 * (M.c_map + 1) * work)%N
        end.
        assert (Hunit : (1 <= work)%N) by (unfold work; lia).
        assert (Hget_work : (get_clock <= M.c_map * work)%N).
        { eapply N.le_trans; [exact Hget|]. apply N.mul_le_mono_l.
          unfold work. lia. }
        assert (Hmerge_work : (merge_clock <= M.c_map * (8 + 1) * 2 * work)%N).
        { eapply N.le_trans; [exact Hmerge|]. apply N.mul_le_mono_l.
          unfold work. lia. }
        assert (Hbudget : ((M.c_map + M.c_map * (8 + 1) * 2 + 2) * work <=
          32 * (M.c_map + 1) * work)%N).
        { apply N.mul_le_mono_r. lia. }
        repeat rewrite N.mul_add_distr_r in Hbudget.
        rewrite ?N.mul_1_l in Hbudget.
        clear Hget Hmerge. clearbody work. lia.
      + pose proof (M.T_get_le Z k row) as Hget.
        set (lookup_bits := K.bits k + 1) in *.
        set (source_work := code_work (fun _ : Z => 0) row) in *.
        clearbody lookup_bits source_work.
        unfold T_round_row, T_relax_row. cbn beta iota zeta. rewrite Ha. cbn beta iota zeta.
        set (get_clock := M.T_get k row) in *. clearbody get_clock. clear Ha.
        unfold row_time_factor.
        repeat rewrite Nat2N.inj_add in Hget.
        repeat rewrite Nat2N.inj_add.
        set (work := (N.of_nat lookup_bits + N.of_nat source_work + 0 + 1)%N).
        match goal with
        | |- N.le ?clock _ => change (clock <= 32 * (M.c_map + 1) * work)%N
        end.
        assert (Hunit : (1 <= work)%N) by (unfold work; lia).
        assert (Hget_work : (get_clock <= M.c_map * work)%N).
        { eapply N.le_trans; [exact Hget|]. apply N.mul_le_mono_l.
          unfold work. lia. }
        assert (Hbudget : ((M.c_map + 2) * work <= 32 * (M.c_map + 1) * work)%N).
        { apply N.mul_le_mono_r. lia. }
        rewrite N.mul_add_distr_r in Hbudget. rewrite ?N.mul_1_l in Hbudget.
        clear Hget. clearbody work. lia.
    - unfold row_time_factor. time_step.
  Qed.

  Lemma row_get_bits : forall m p row k a,
    M.find p m = Some row -> M.get k row = Some a -> Z.size_nat a <= ell m.
  Proof.
    intros m p row k a Hrow Ha. apply (ell_entry m p (K.encode k) a).
    unfold raw_entry. rewrite Hrow. cbn [row_of]. now rewrite <- M.get_find.
  Qed.

  (** Pivot work charges each source skeleton once and one supported pivot row. *)
  Lemma pivot_row_work_bound : forall m k row, In row (rows m) ->
    pivot_row_work k (row_of (M.get k m)) row <=
      M.nodes row + K.bits k + 1 + supp m * (b m + 2 * ell m + 4).
  Proof.
    intros m k row Hin.
    assert (Hsupport : forall q, In q (M.codes row) -> In q (support m)).
    { intros q Hq. apply support_spec. right. apply in_flat_map. exists row. now split. }
    pose proof (codes_support_length Z row m Hsupport) as Hcount.
    apply rows_find in Hin. destruct Hin as [p Hrow].
    unfold pivot_row_work. rewrite code_work_zero.
    replace (supp m * (b m + 2 * ell m + 4)) with
      (supp m + supp m * (b m + 2 * ell m + 3)) by ring.
    destruct (M.get k row) as [a|] eqn:Ha.
    - pose proof (row_get_bits m p row k a Hrow Ha) as Hprefix.
      pose proof (code_work_bits_bound m (row_of (M.get k m)) (Z.size_nat a) (ell m)
        (row_lookup_support m k) (row_lookup_bits m k)) as Hexit.
      assert (Hexit_cap : code_work (fun z => Z.size_nat a + Z.size_nat z + 1)
        (row_of (M.get k m)) <= supp m * (b m + 2 * ell m + 3)).
      { eapply Nat.le_trans; [exact Hexit|]. apply Nat.mul_le_mono_l. lia. }
      clear Hexit Hrow Ha Hsupport. lia.
    - lia.
  Qed.

  (** A positive quadratic budget covers the number of supported codes. *)
  Lemma quadratic_work_count : forall n payload, 1 <= payload ->
    n <= (n + 1)^2 * payload.
  Proof.
    intros n payload Hpositive. eapply Nat.le_trans with ((n + 1)^2).
    - cbn [Nat.pow]. nia.
    - replace ((n + 1)^2) with (((n + 1)^2) * 1) at 1 by ring.
      now apply Nat.mul_le_mono_l.
  Qed.

  (** Summing a linear row allowance over the support yields a quadratic allowance. *)
  Lemma quadratic_work_rows : forall n payload factor rowwork,
    rowwork <= factor * (n + 1) * payload ->
    n * rowwork <= factor * (n + 1)^2 * payload.
  Proof.
    intros n payload factor rowwork Hrow.
    eapply Nat.le_trans; [apply Nat.mul_le_mono_l; exact Hrow|].
    replace (n * (factor * (n + 1) * payload)) with
      (factor * (n * (n + 1)) * payload) by ring.
    apply Nat.mul_le_mono_r, Nat.mul_le_mono_l. cbn [Nat.pow]. nia.
  Qed.

  (** Pivot lookup and payload units fit four linear support allowances. *)
  Lemma pivot_scalar_work_bound : forall n bb kk ee,
    kk + 1 + n * (bb + 2 * ee + 4) <= 4 * (n + 1) * (bb + kk + ee + 1).
  Proof.
    intros n bb kk ee. nia.
  Qed.

  (** Summing pivot callbacks preserves an additive charge for the source skeleton. *)
  Lemma pivot_matrix_work_bound : forall m k,
    code_work (pivot_row_work k (row_of (M.get k m))) m <=
      6 * (supp m + 1)^2 * (b m + K.bits k + ell m + 1).
  Proof.
    intros m k.
    assert (Hcount : length (M.codes m) <= supp m).
    { apply codes_support_length. intros p Hp. apply support_spec. now left. }
    pose proof (rows_length m) as Hrows.
    assert (Hsum : sum_weight (pivot_row_work k (row_of (M.get k m))) (rows m) <=
      sum_weight (fun row => M.nodes row +
        (K.bits k + 1 + supp m * (b m + 2 * ell m + 4))) (rows m)).
    { apply sum_weight_mono. intros row Hin.
      pose proof (pivot_row_work_bound m k row Hin). lia. }
    rewrite sum_weight_add, sum_weight_const in Hsum.
    change (sum_weight (pivot_row_work k (row_of (M.get k m))) (rows m) <=
      sum_weight M.nodes (rows m) + length (rows m) *
        (K.bits k + 1 + supp m * (b m + 2 * ell m + 4))) in Hsum.
    assert (Hprod : length (rows m) * (K.bits k + 1 +
      supp m * (b m + 2 * ell m + 4)) <=
      supp m * (K.bits k + 1 + supp m * (b m + 2 * ell m + 4))).
    { apply Nat.mul_le_mono_r. lia. }
    pose proof (skel_le m) as Hskel.
    change (M.nodes m + sum_weight M.nodes (rows m) <=
      (supp m + 1)^2 * (b m + 1)) in Hskel.
    unfold code_work at 1. rewrite stored_weight_rows.
    set (units := (supp m + 1)^2 * (b m + K.bits k + ell m + 1)).
    replace (6 * (supp m + 1)^2 * (b m + K.bits k + ell m + 1)) with
      (6 * units) by (unfold units; ring).
    assert (Hcount_units : supp m <= units).
    { unfold units. apply quadratic_work_count. lia. }
    assert (Hskel_units : M.nodes m + sum_weight M.nodes (rows m) <= units).
    { eapply Nat.le_trans; [exact Hskel|]. unfold units. apply Nat.mul_le_mono_l. lia. }
    assert (Hprod_units : length (rows m) * (K.bits k + 1 +
      supp m * (b m + 2 * ell m + 4)) <= 4 * units).
    { eapply Nat.le_trans; [exact Hprod|]. unfold units.
      replace (4 * ((supp m + 1)^2 * (b m + K.bits k + ell m + 1))) with
        (4 * (supp m + 1)^2 * (b m + K.bits k + ell m + 1)) by ring.
      apply quadratic_work_rows, pivot_scalar_work_bound. }
    clear Hskel Hprod Hrows. clearbody units. lia.
  Qed.


  Lemma quadratic_payload_le : forall n payload,
    payload <= (n + 1)^2 * payload.
  Proof.
    intros n payload. replace payload with (1 * payload) at 1 by ring.
    apply Nat.mul_le_mono_r. cbn [Nat.pow]. nia.
  Qed.

  (** A merge against an empty right input charges only present left payloads. *)
  Lemma T_merge_left_code_work : forall (A B C : Type)
      (f : option A -> option B -> option C) tf (w : A -> nat) (m : M.t A) c,
    (forall a b, (tf a b <= c * N.of_nat (option_weight w a + 1))%N) ->
    (M.T_merge f tf m (@M.empty B) <= M.c_map * (c + 1) * 2 *
      N.of_nat (code_work w m + 1))%N.
  Proof.
    intros A B C f tf w m c Hbound.
    assert (Hcallback : forall a b,
      (tf a b <= c * N.of_nat (option_weight w a +
        option_weight (fun _ : B => 0%nat) b + 1))%N).
    { intros a b. rewrite option_weight_zero, Nat.add_0_r. apply Hbound. }
    pose proof (T_merge_code_work A B C f tf w (fun _ : B => 0) m M.empty c Hcallback)
      as Hmerge. rewrite code_work_empty, Nat.add_0_r in Hmerge. exact Hmerge.
  Qed.

  (** A sparse pivot update uses a quadratic raw-support work budget. *)
  Definition relax_time_factor : N := (512 * (M.c_map + 1) * (M.c_map + 1))%N.

  (** One relaxation pays for one pivot-row lookup and the supported row updates. *)
  Lemma round_clocks_bound : forall k m,
    (M.T_get k m + T_row_of (M.get k m) +
      M.T_merge (round_row k (row_of (M.get k m)))
        (fun x y => T_round_row k (row_of (M.get k m)) x y) m M.empty + 1 <= relax_time_factor * N.of_nat
      ((supp m + 1)^2 * (b m + K.bits k + ell m + 1)))%N.
  Proof.
    intros k m.
    set (units := (supp m + 1)^2 * (b m + K.bits k + ell m + 1)).
    match goal with
    | |- N.le ?clock _ => change (clock <= relax_time_factor * N.of_nat units)%N
    end.
    assert (Hkey : K.bits k + 1 <= units).
    { unfold units. eapply Nat.le_trans; [|apply quadratic_payload_le]. lia. }
    assert (Hpositive : 1 <= units) by lia.
    pose proof (pivot_matrix_work_bound m k) as Hmatrix.
    replace (6 * (supp m + 1)^2 * (b m + K.bits k + ell m + 1)) with
      (6 * units) in Hmatrix by (unfold units; ring).
    assert (Hdata : code_work (pivot_row_work k (row_of (M.get k m))) m + 1 <= 7 * units).
    { lia. }
    pose proof (time_of_nat_le _ _ Hdata) as HdataN. rewrite Nat2N.inj_mul in HdataN.
    pose proof (time_of_nat_le _ _ Hkey) as HkeyN.
    set (work := N.of_nat units) in *.
    assert (Hwork : (1 <= work)%N) by (unfold work; lia).
    clear Hpositive Hkey Hmatrix Hdata. clearbody work. clear units.
    pose proof (T_merge_left_code_work (M.t Z) (M.t Z) (M.t Z)
      (round_row k (row_of (M.get k m)))
      (fun x y => T_round_row k (row_of (M.get k m)) x y)
      (pivot_row_work k (row_of (M.get k m))) m row_time_factor
      (T_round_row_le k (row_of (M.get k m)))) as Hmerge.
    assert (Hmerge' : (M.T_merge (round_row k (row_of (M.get k m)))
      (fun x y => T_round_row k (row_of (M.get k m)) x y) m M.empty <=
      M.c_map * (row_time_factor + 1) * 2 * (7 * work))%N).
    { eapply N.le_trans; [exact Hmerge|]. apply N.mul_le_mono_l. exact HdataN. }
    assert (Hget : (M.T_get k m <= M.c_map * work)%N).
    { eapply N.le_trans; [apply M.T_get_le|]. apply N.mul_le_mono_l. exact HkeyN. }
    pose proof (T_row_of_le (M.get k m)) as Hrow.
    assert (Hcoefficient : (M.c_map * (row_time_factor + 1) * 2 * 7 + M.c_map + 4 <=
      relax_time_factor)%N).
    { unfold row_time_factor, relax_time_factor. nia. }
    pose proof (N.mul_le_mono_r _ _ work Hcoefficient) as Hbudget.
    clear Hmerge HdataN HkeyN Hcoefficient.
    replace (M.c_map * (row_time_factor + 1) * 2 * (7 * work))%N with
      ((M.c_map * (row_time_factor + 1) * 2 * 7) * work)%N in Hmerge' by ring.
    repeat rewrite N.mul_add_distr_r in Hbudget.
    lia.
  Qed.

  (** Pivot-presence checking charges lookup bits only at finite outer rows. *)
  Lemma T_pivot_present_small : forall k m,
    (T_pivot_present k m <= 8 * (M.c_map + 1) * (M.c_map + 1) * N.of_nat
      (M.nodes m + length (M.codes m) * (K.bits k + 2) + K.bits k + 1))%N.
  Proof.
    intros k m.
    set (units := M.nodes m + length (M.codes m) * (K.bits k + 2) + K.bits k + 1).
    change (T_pivot_present k m <=
      8 * (M.c_map + 1) * (M.c_map + 1) * N.of_nat units)%N.
    assert (Hpositive : 1 <= units) by (unfold units; lia).
    assert (Hkey : K.bits k + 1 <= units) by (unfold units; lia).
    assert (Hweight : stored_weight (fun _ : M.t Z => K.bits k + 1) m <=
      length (M.codes m) * (K.bits k + 1)).
    { apply stored_weight_uniform. intros p row Hrow. lia. }
    assert (Hdata : code_work (fun _ : M.t Z => K.bits k + 1) m + 1 <= units).
    { unfold code_work, units.
      replace (length (M.codes m) * (K.bits k + 2)) with
        (length (M.codes m) * (K.bits k + 1) + length (M.codes m)) by ring.
      lia. }
    pose proof (time_of_nat_le _ _ Hdata) as HdataN.
    pose proof (time_of_nat_le _ _ Hkey) as HkeyN.
    set (work := N.of_nat units) in *.
    assert (Hwork : (1 <= work)%N) by (unfold work; lia).
    clear Hpositive Hkey Hweight Hdata. clearbody work. clear units.
    pose proof (T_existsb_code_work (M.t Z) (column_present k)
      (fun row => T_column_present k row) (fun _ : M.t Z => K.bits k + 1)
      m (4 * (M.c_map + 1))%N (T_column_present_small k)) as Hscan.
    assert (Hscan' : (M.T_existsb (column_present k) (fun row => T_column_present k row) m <=
      M.c_map * (4 * (M.c_map + 1) + 1) * work)%N).
    { eapply N.le_trans; [exact Hscan|]. apply N.mul_le_mono_l. exact HdataN. }
    assert (Hget : (M.T_get k m <= M.c_map * work)%N).
    { eapply N.le_trans; [apply M.T_get_le|]. apply N.mul_le_mono_l. exact HkeyN. }
    assert (Hcoefficient : (M.c_map * (4 * (M.c_map + 1) + 1) + M.c_map + 4 <=
      8 * (M.c_map + 1) * (M.c_map + 1))%N) by nia.
    pose proof (N.mul_le_mono_r _ _ work Hcoefficient) as Hbudget.
    clear Hscan HdataN HkeyN Hcoefficient.
    repeat rewrite N.mul_add_distr_r in Hbudget.
    unfold T_pivot_present. cbn beta iota zeta.
    destruct (M.get k m); cbn beta iota zeta; lia.
  Qed.

  (** Pivot-presence work fits the same quadratic budget as the round. *)
  Lemma pivot_test_work_bound : forall k m,
    M.nodes m + length (M.codes m) * (K.bits k + 2) + K.bits k + 1 <=
      3 * ((supp m + 1)^2 * (b m + K.bits k + ell m + 1)).
  Proof.
    intros k m.
    assert (Hsupport : forall p, In p (M.codes m) -> In p (support m)).
    { intros p Hp. apply support_spec. now left. }
    pose proof (nodes_support (M.t Z) m m Hsupport) as Hnodes.
    pose proof (codes_support_length (M.t Z) m m Hsupport) as Hcount.
    cbn [Nat.pow]. nia.
  Qed.

  (** Materializing a supported diagonal preserves the raw support size and key bits. *)
  Lemma seed_round_sizes : forall k m, pivot_present k m = true ->
    supp (put k k (lower_bound 0%Z (entry m k k)) m) = supp m /\
    b (put k k (lower_bound 0%Z (entry m k k)) m) = b m.
  Proof.
    intros k m Hpresent. apply pivot_present_support in Hpresent. apply support_sizes.
    intro p. rewrite support_put. split.
    - intros [Heq|[Heq|Hin]]; subst; assumption.
    - intro Hin. right. now right.
  Qed.

  (** The signed round's inline diagonal seed and sparse merge fit one raw-support allowance. *)
  Lemma T_fw_round_raw : forall k m,
    (T_fw_round k m <= 1024 * (M.c_map + 1) * (M.c_map + 1) * N.of_nat
      ((supp m + 1)^2 * (b m + K.bits k + ell m + 1)))%N.
  Proof.
    intros k m.
    set (units := (supp m + 1)^2 * (b m + K.bits k + ell m + 1)).
    change (T_fw_round k m <=
      1024 * (M.c_map + 1) * (M.c_map + 1) * N.of_nat units)%N.
    assert (Hkey : K.bits k + 1 <= units).
    { unfold units. eapply Nat.le_trans; [|apply quadratic_payload_le]. lia. }
    assert (Hpositive : 1 <= units) by lia.
    pose proof (pivot_test_work_bound k m) as Htest. fold units in Htest.
    pose proof (time_of_nat_le _ _ Htest) as HtestN. rewrite Nat2N.inj_mul in HtestN.
    pose proof (time_of_nat_le _ _ Hkey) as HkeyN.
    set (work := N.of_nat units) in *.
    assert (Hwork : (1 <= work)%N) by (unfold work; lia).
    assert (Hpresent : (T_pivot_present k m <=
      24 * (M.c_map + 1) * (M.c_map + 1) * work)%N).
    { eapply N.le_trans; [apply T_pivot_present_small|].
      replace (24 * (M.c_map + 1) * (M.c_map + 1) * work)%N with
        (8 * (M.c_map + 1) * (M.c_map + 1) * (3 * work))%N by ring.
      apply N.mul_le_mono_l. exact HtestN. }
    assert (Htwo_keys : (N.of_nat (K.bits k + K.bits k + 1) <= 2 * work)%N).
    { rewrite !Nat2N.inj_add in HkeyN |- *. lia. }
    assert (Hinsert : (T_entry m k k + T_lower_bound 0%Z (entry m k k) +
      T_put k k (lower_bound 0%Z (entry m k k)) m <=
      64 * (M.c_map + 1) * work)%N).
    { assert (Hentry : (T_entry m k k <= 16 * (M.c_map + 1) * work)%N).
      { eapply N.le_trans; [apply T_entry_small|].
        replace (16 * (M.c_map + 1) * work)%N with
          (8 * (M.c_map + 1) * (2 * work))%N by ring.
        apply N.mul_le_mono_l. exact Htwo_keys. }
      assert (Hput : (T_put k k (lower_bound 0%Z (entry m k k)) m <=
        32 * (M.c_map + 1) * work)%N).
      { eapply N.le_trans; [apply T_put_le|].
        replace (32 * (M.c_map + 1) * work)%N with
          (16 * (M.c_map + 1) * (2 * work))%N by ring.
        apply N.mul_le_mono_l. exact Htwo_keys. }
      pose proof (T_lower_bound_le 0%Z (entry m k k)) as Hlower.
      change (T_lower_bound 0%Z (entry m k k) <= 5)%N in Hlower.
      assert (Hcoefficient : (16 * (M.c_map + 1) + 32 * (M.c_map + 1) + 5 <=
        64 * (M.c_map + 1))%N) by lia.
      pose proof (N.mul_le_mono_r _ _ work Hcoefficient) as Hbudget.
      rewrite !N.mul_add_distr_r in Hbudget.
      clearbody work. clear - Hentry Hput Hlower Hwork Hbudget. lia. }
    assert (Hcoefficient : (relax_time_factor +
      24 * (M.c_map + 1) * (M.c_map + 1) + 64 * (M.c_map + 1) + 8 <=
      1024 * (M.c_map + 1) * (M.c_map + 1))%N).
    { unfold relax_time_factor. nia. }
    pose proof (N.mul_le_mono_r _ _ work Hcoefficient) as Hbudget.
    rewrite !N.mul_add_distr_r in Hbudget.
    destruct (pivot_present k m) eqn:Hcheck.
    - set (seed := put k k (lower_bound 0%Z (entry m k k)) m).
      destruct (seed_round_sizes k m Hcheck) as [Hsupport Hbits].
      fold seed in Hsupport, Hbits.
      assert (Hell : ell seed <= ell m).
      { unfold seed. apply ell_put; [lia|]. apply lower_bound_ell; [lia|].
        change (0 <= ell m). lia. }
      assert (Hrelax : (M.T_get k seed + T_row_of (M.get k seed) +
        M.T_merge (round_row k (row_of (M.get k seed)))
          (fun x y => T_round_row k (row_of (M.get k seed)) x y) seed M.empty + 1 <=
        relax_time_factor * work)%N).
      { eapply N.le_trans; [apply round_clocks_bound|]. apply N.mul_le_mono_l.
        unfold work, units. apply time_of_nat_le. rewrite Hsupport, Hbits.
        apply Nat.mul_le_mono_l. lia. }
      clear Hpositive Hkey Htest HtestN HkeyN Htwo_keys Hcoefficient Hsupport Hbits Hell.
      clearbody work. clear units. unfold T_fw_round. rewrite Hcheck.
      cbn beta iota zeta. fold seed. lia.
    - pose proof (round_clocks_bound k m) as Hrelax.
      match type of Hrelax with
      | N.le ?clock _ => change (clock <= relax_time_factor * work)%N in Hrelax
      end.
      clear Hpositive Hkey Htest HtestN HkeyN Htwo_keys Hcoefficient.
      clearbody work. clear units. unfold T_fw_round. rewrite Hcheck.
      cbn beta iota zeta. lia.
  Qed.

  Lemma T0_fw_round : forall k m, dbm_wf m ->
    (T_fw_round k m <= k_octagon * N.of_nat
      ((supp m + 1)^2 * (b m + K.bits k + ell m + 1)))%N.
  Proof.
    intros k m Hwf. eapply N.le_trans; [apply T_fw_round_raw|].
    apply N.mul_le_mono_r. unfold k_octagon. nia.
  Qed.


  (** Every supported code has its key in a well-formed pivot enumeration. *)
  Lemma keys_cover : forall m k, dbm_wf m ->
    In (K.encode k) (support m) -> In k (keys m).
  Proof.
    intros m k [Houter Hrows] Hsupport. unfold keys.
    rewrite (dedup_membership K.t K.eqb key_eqb_true).
    left. apply in_app_iff. apply support_find in Hsupport.
    destruct Hsupport as [Hrow|[p Hraw]].
    - left. destruct (M.find (K.encode k) m) as [row|] eqn:Hfound;
        [|contradiction].
      apply in_map_iff. exists (k, row). split; [reflexivity|].
      apply (proj2 (M.elements_spec (M.t Z) m k row Houter)).
      now rewrite M.get_find.
    - right. unfold raw_entry in Hraw.
      destruct (M.find p m) as [row|] eqn:Hrow; cbn [row_of] in Hraw.
      + destruct (M.wf_find (M.t Z) m p row Houter Hrow) as [i Hi].
        apply in_flat_map. exists (i, row). split.
        * apply (proj2 (M.elements_spec (M.t Z) m i row Houter)).
          now rewrite M.get_find, Hi.
        * cbn [snd]. destruct (M.find (K.encode k) row) as [z|] eqn:Hentry;
            [|contradiction].
          apply in_map_iff. exists (k, z). split; [reflexivity|].
          apply (proj2 (M.elements_spec Z row k z (Hrows p row Hrow))).
          now rewrite M.get_find.
      + rewrite M.find_empty in Hraw. contradiction.
  Qed.

  (** Successful full Floyd closure is below the seeded old matrix. *)
  Lemma fw_below_incremental_seed : forall m i j d, dbm_wf m ->
    let direct := add_cons i j d m in
    forallb (fun k => nonnegative k (fw direct)) (keys direct) = true ->
    forall a b, RelationalPathBounds.below (entry (fw direct) a b)
      (entry (add_cons j j 0%Z (add_cons i i 0%Z m)) a b).
  Proof.
    intros m i j d Hwf. cbn beta iota zeta.
    set (direct := add_cons i j d m). intro Hscan.
    assert (Hwfdirect : dbm_wf direct).
    { unfold direct. now apply add_cons_wf. }
    assert (Hinv : RelationalPathBounds.invariant (entry direct)
      (entry (fw direct)) (rev (keys direct))).
    { unfold fw. rewrite pivot_keys_eq_keys.
      replace (rev (keys direct)) with (rev (keys direct) ++ nil)
        by now rewrite app_nil_r.
      apply fw_pivots_success_path_invariant.
      - apply RelationalPathBounds.invariant_initial.
      - intros k Hkey. now apply keys_support.
      - intros k Hkey. rewrite forallb_forall in Hscan.
        unfold fw in Hscan. rewrite pivot_keys_eq_keys in Hscan.
        now apply Hscan. }
    destruct Hinv as [Hbelow Hclosed Hzero Hpath].
    assert (Hdiag : forall p, In (K.encode p) (support direct) ->
      entry (fw direct) p p = Some 0%Z).
    { intros p Hp. apply Hzero. apply in_rev. rewrite rev_involutive.
      now apply keys_cover. }
    assert (Hendpoints : forall p, p = i \/ p = j \/ p = flip i \/ p = flip j ->
      entry (fw direct) p p = Some 0%Z).
    { intros p [Hp|[Hp|[Hp|Hp]]]; subst p; apply Hdiag;
        unfold direct; rewrite support_add_cons; tauto. }
    intros a b. eapply below_add_zero.
    - eapply below_add_zero.
      + intros x y. eapply RelationalPathBounds.below_trans;
          [apply Hbelow|apply add_cons_entry_below].
      + apply Hendpoints. now left.
      + apply Hendpoints. now right; right; left.
    - apply Hendpoints. now right; left.
    - apply Hendpoints. now right; right; right.
  Qed.

  Lemma keys_support_iff : forall m k, dbm_wf m ->
    (In k (keys m) <-> In (K.encode k) (support m)).
  Proof.
    intros m k Hwf. split; [now apply keys_support|now apply keys_cover].
  Qed.

  (** Every performed pivot round preserves the same support. *)
  Lemma fw_pivots_support : forall ks m p,
    In p (support (fw_pivots ks m)) <-> In p (support m).
  Proof.
    induction ks as [|k ks IH]; intros m p; [reflexivity|].
    cbn [fw_pivots]. destruct (nonnegative k (fw_round k m)).
    - rewrite IH. apply support_round.
    - apply support_round.
  Qed.

  Lemma fw_support : forall m p, In p (support (fw m)) <-> In p (support m).
  Proof.
    intros m p. unfold fw. apply fw_pivots_support.
  Qed.

  Lemma fw_sizes : forall m, supp (fw m) = supp m /\ b (fw m) = b m.
  Proof.
    intro m. apply support_sizes, fw_support.
  Qed.

  Lemma fw_keys : forall m, fw m = fw_pivots (keys m) m.
  Proof.
    intro m. unfold fw. now rewrite pivot_keys_eq_keys.
  Qed.

  (** A successful full scan leaves every original support key processed. *)
  Lemma fw_success_path_invariant : forall m, dbm_wf m ->
    forallb (fun k => nonnegative k (fw m)) (keys m) = true ->
    RelationalPathBounds.invariant (entry m) (entry (fw m)) (rev (keys m)).
  Proof.
    intros m Hwf Hscan. rewrite fw_keys in Hscan |- *.
    replace (rev (keys m)) with (rev (keys m) ++ nil) by now rewrite app_nil_r.
    apply fw_pivots_success_path_invariant.
    - apply RelationalPathBounds.invariant_initial.
    - intros k Hkey. now apply keys_support.
    - intros k Hkey. rewrite forallb_forall in Hscan.
      now apply Hscan.
  Qed.

  (** Paired shortest paths make a successful full Floyd result coherent. *)
  Lemma coherent_fw_success : forall m, dbm_wf m -> coherent m -> bar_closed m ->
    forallb (fun k => nonnegative k (fw m)) (keys m) = true -> coherent (fw m).
  Proof.
    intros m Hwf Hcoh Hbar Hscan.
    pose proof (fw_success_path_invariant m Hwf Hscan) as Hinv.
    destruct Hinv as [Hbelow Hclosed Hzero Hpath].
    assert (Hkeys : forall k, In k (rev (keys m)) -> In (bar k) (rev (keys m))).
    { intros k Hk. apply in_rev in Hk. apply in_rev.
      rewrite rev_involutive.
      apply (proj2 (keys_support_iff m (bar k) Hwf)).
      apply Hbar, (proj1 (keys_support_iff m k Hwf)). exact Hk. }
    assert (Hpair : forall i j,
      RelationalPathBounds.below (entry (fw m) (bar j) (bar i)) (entry (fw m) i j)).
    { intros i j. destruct (entry (fw m) i j) as [d|] eqn:Hentry;
        [|destruct (entry (fw m) (bar j) (bar i)); exact I].
      pose proof (coherent_path_pair m (rev (keys m)) i j d Hcoh Hkeys
        (Hpath i j d Hentry)) as Hpaired.
      destruct Hpaired as [[Heq Hd]|[ks [Hks Hchain]]].
      - subst d. rewrite <- Heq.
        assert (Hsupport : In (K.encode (bar j)) (support m)).
        { apply Hbar. apply (proj1 (fw_support m (K.encode j))).
          eapply entry_target_support. exact Hentry. }
        rewrite (Hzero (bar j)).
        + cbn [RelationalPathBounds.below]. lia.
        + apply in_rev. rewrite rev_involutive.
          apply (proj2 (keys_support_iff m (bar j) Hwf)).
          exact Hsupport.
      - pose proof (RelationalPathBounds.chain_bound K.t (entry m) (entry (fw m))
          (rev (keys m)) Hbelow Hclosed ks (bar j) (bar i) Hks) as Hbound.
        now rewrite Hchain in Hbound. }
    assert (Hbarbar : forall x, bar (bar x) = x).
    { intro x. exact (flip_involutive x). }
    intros i j. apply RelationalPathBounds.below_antisym.
    - pose proof (Hpair (bar j) (bar i)) as Hreverse.
      now rewrite !Hbarbar in Hreverse.
    - exact (Hpair i j).
  Qed.

  (** A completed successful scan has zero diagonals and every triangle bound. *)
  Lemma fw_closed_success : forall m, dbm_wf m ->
    forallb (fun k => nonnegative k (fw m)) (keys m) = true ->
    (forall i, In (K.encode i) (support (fw m)) -> entry (fw m) i i = Some 0%Z) /\
    (forall i j k a z, entry (fw m) i k = Some a ->
      entry (fw m) k j = Some z ->
      exists d, entry (fw m) i j = Some d /\ (d <= a + z)%Z).
  Proof.
    intros m Hwf Hscan.
    pose proof (fw_success_path_invariant m Hwf Hscan) as Hinv.
    destruct Hinv as [_ Hclosed Hzero _]. split.
    - intros i Hsupport. apply Hzero.
      apply in_rev. rewrite rev_involutive.
      apply (proj2 (keys_support_iff m i Hwf)).
      apply (proj1 (fw_support m (K.encode i))). exact Hsupport.
    - intros i j k a z Hik Hkj.
      assert (Hkey : In k (rev (keys m))).
      { apply in_rev. rewrite rev_involutive.
        apply (proj2 (keys_support_iff m k Hwf)).
        apply (proj1 (fw_support m (K.encode k))).
        eapply entry_target_support. exact Hik. }
      pose proof (Hclosed k Hkey i j) as Hbound.
      rewrite Hik, Hkj in Hbound. cbn [RelationalPathBounds.plus] in Hbound.
      destruct (RelationalPathBounds.below_finite _ _ Hbound)
        as [d [Hd Hle]]. exists d. now split.
  Qed.

  Lemma fw_closed_at_success : forall m, dbm_wf m ->
    forallb (fun k => nonnegative k (fw m)) (keys m) = true ->
    forall k, RelationalPathBounds.closed_at (entry (fw m)) k.
  Proof.
    intros m Hwf Hscan k i j.
    destruct (entry (fw m) i k) as [a|] eqn:Hik;
      destruct (entry (fw m) k j) as [z|] eqn:Hkj;
      cbn [RelationalPathBounds.plus RelationalPathBounds.below];
      try (destruct (entry (fw m) i j); exact I).
    destruct (proj2 (fw_closed_success m Hwf Hscan) i j k a z Hik Hkj)
      as [d [Hd Hle]]. rewrite Hd.
    cbn [RelationalPathBounds.below]. exact Hle.
  Qed.

  (** Successful full Floyd entries lie below all four incremental paths. *)
  Lemma fw_below_incremental_candidate : forall m i j d, dbm_wf m ->
    tightly_closed m ->
    let direct := add_cons i j d m in
    let seed := add_cons j j 0%Z (add_cons i i 0%Z m) in
    forallb (fun k => nonnegative k (fw direct)) (keys direct) = true ->
    matrix_ok (increment_matrix i j d seed) = true ->
    forall a b, RelationalPathBounds.below (entry (fw direct) a b)
      (entry (increment_matrix i j d seed) a b).
  Proof.
    intros m i j d Hwf Htight. cbn beta iota zeta.
    set (direct := add_cons i j d m).
    set (seed := add_cons j j 0%Z (add_cons i i 0%Z m)).
    intros Hfwscan Hscan a b.
    assert (Hwfdirect : dbm_wf direct).
    { unfold direct. now apply add_cons_wf. }
    pose proof (fw_closed_at_success direct Hwfdirect Hfwscan) as Hclosed.
    pose proof (fw_below_incremental_seed m i j d Hwf Hfwscan) as Hseed.
    change (forall x y, RelationalPathBounds.below
      (entry (fw direct) x y) (entry seed x y)) in Hseed.
    destruct (fw_success_path_invariant direct Hwfdirect Hfwscan)
      as [Hbelow_direct _ _ _].
    destruct (add_cons_inserted_bounds m i j d) as [Hfirst Hsecond].
    assert (Hedge1 : RelationalPathBounds.below
      (entry (fw direct) i j) (Some d)).
    { eapply RelationalPathBounds.below_trans;
        [apply Hbelow_direct|exact Hfirst]. }
    assert (Hedge2 : RelationalPathBounds.below
      (entry (fw direct) (flip j) (flip i)) (Some d)).
    { eapply RelationalPathBounds.below_trans;
        [apply Hbelow_direct|exact Hsecond]. }
    pose proof (closed_below_edge_extension (entry (fw direct))
      (entry seed) i j d Hclosed Hseed Hedge1) as Hone.
    pose proof (closed_below_edge_extension (entry (fw direct))
      (RelationalPathBounds.edge_extension (entry seed) i j d)
      (flip j) (flip i) d Hclosed Hone Hedge2 a b) as Htwo.
    pose proof (incremental_mixed_cycle m i j d Hwf Htight Hscan) as Hmixed.
    change (RelationalPathBounds.below (Some 0%Z)
      (twin_path d (Some 0%Z) (entry seed j (flip j))
        (entry seed (flip i) i))) in Hmixed.
    rewrite (incremental_sequential_extension seed i j d Hmixed a b).
    exact Htwo.
  Qed.

  (** Passing incremental and full Floyd passes have identical entries. *)
  Lemma incremental_fw_equal : forall m i j d, dbm_wf m -> tightly_closed m ->
    let direct := add_cons i j d m in
    let seed := add_cons j j 0%Z (add_cons i i 0%Z m) in
    matrix_ok (increment_matrix i j d seed) = true ->
    forallb (fun k => nonnegative k (fw direct)) (keys direct) = true /\
      forall a b, entry (increment_matrix i j d seed) a b =
        entry (fw direct) a b.
  Proof.
    intros m i j d Hwf Htight. cbn beta iota zeta.
    set (direct := add_cons i j d m).
    set (seed := add_cons j j 0%Z (add_cons i i 0%Z m)).
    intro Hscan.
    pose proof (incremental_candidate_fw_scan m i j d Hwf Htight Hscan)
      as Hfwscan.
    change (forallb (fun k => nonnegative k (fw direct)) (keys direct) = true)
      in Hfwscan.
    split; [exact Hfwscan|]. intros a b.
    apply RelationalPathBounds.below_antisym.
    - exact (incremental_candidate_below_fw m i j d Hwf Htight Hscan a b).
    - exact (fw_below_incremental_candidate m i j d Hwf Htight
        Hfwscan Hscan a b).
  Qed.

  (** A successful full Floyd scan excludes the mixed signed-edge cycle. *)
  Lemma fw_mixed_cycle : forall m i j d, dbm_wf m ->
    let direct := add_cons i j d m in
    let seed := add_cons j j 0%Z (add_cons i i 0%Z m) in
    forallb (fun k => nonnegative k (fw direct)) (keys direct) = true ->
    RelationalPathBounds.below (Some 0%Z)
      (twin_path d (Some 0%Z) (entry seed j (flip j))
        (entry seed (flip i) i)).
  Proof.
    intros m i j d Hwf. cbn beta iota zeta.
    set (direct := add_cons i j d m).
    set (seed := add_cons j j 0%Z (add_cons i i 0%Z m)).
    intro Hscan.
    assert (Hwfdirect : dbm_wf direct).
    { unfold direct. now apply add_cons_wf. }
    pose proof (fw_closed_at_success direct Hwfdirect Hscan) as Hclosed.
    pose proof (fw_below_incremental_seed m i j d Hwf Hscan) as Hseed.
    change (forall x y, RelationalPathBounds.below
      (entry (fw direct) x y) (entry seed x y)) in Hseed.
    destruct (fw_success_path_invariant direct Hwfdirect Hscan)
      as [Hbelow_direct _ _ _].
    destruct (add_cons_inserted_bounds m i j d) as [Hfirst Hsecond].
    assert (Hedge1 : RelationalPathBounds.below
      (entry (fw direct) i j) (Some d)).
    { eapply RelationalPathBounds.below_trans;
        [apply Hbelow_direct|exact Hfirst]. }
    assert (Hedge2 : RelationalPathBounds.below
      (entry (fw direct) (flip j) (flip i)) (Some d)).
    { eapply RelationalPathBounds.below_trans;
        [apply Hbelow_direct|exact Hsecond]. }
    pose proof (closed_below_edge_extension (entry (fw direct))
      (entry seed) i j d Hclosed Hseed Hedge1 (flip i) (flip j)) as Hone.
    assert (Hzero : entry (fw direct) (flip i) (flip i) = Some 0%Z).
    { apply (proj1 (fw_closed_success direct Hwfdirect Hscan)).
      apply (proj2 (fw_support direct (K.encode (flip i)))).
      unfold direct. rewrite support_add_cons. now right; right; left. }
    pose proof (Hclosed (flip j) (flip i) (flip i)) as Htriangle.
    rewrite Hzero in Htriangle.
    pose proof (RelationalPathBounds.below_trans _ _ _ Htriangle
      (RelationalPathBounds.plus_mono _ _ _ _ Hone Hedge2)) as Hcycle.
    unfold RelationalPathBounds.edge_extension in Hcycle.
    rewrite RelationalPathBounds.plus_minimum_r in Hcycle.
    apply RelationalPathBounds.minimum_glb in Hcycle.
    destruct Hcycle as [_ Hmixed].
    destruct (entry seed (flip i) i) as [back|];
      destruct (entry seed j (flip j)) as [cross|];
      cbn [RelationalPathBounds.plus RelationalPathBounds.below
        twin_path path_sum twin_prefix] in *; try exact I; lia.
  Qed.

  Lemma fw_below_candidate_on_full_scan : forall m i j d, dbm_wf m ->
    let direct := add_cons i j d m in
    let seed := add_cons j j 0%Z (add_cons i i 0%Z m) in
    forallb (fun k => nonnegative k (fw direct)) (keys direct) = true ->
    forall a b, RelationalPathBounds.below (entry (fw direct) a b)
      (entry (increment_matrix i j d seed) a b).
  Proof.
    intros m i j d Hwf. cbn beta iota zeta.
    set (direct := add_cons i j d m).
    set (seed := add_cons j j 0%Z (add_cons i i 0%Z m)).
    intros Hscan a b.
    assert (Hwfdirect : dbm_wf direct).
    { unfold direct. now apply add_cons_wf. }
    pose proof (fw_closed_at_success direct Hwfdirect Hscan) as Hclosed.
    pose proof (fw_below_incremental_seed m i j d Hwf Hscan) as Hseed.
    change (forall x y, RelationalPathBounds.below
      (entry (fw direct) x y) (entry seed x y)) in Hseed.
    destruct (fw_success_path_invariant direct Hwfdirect Hscan)
      as [Hbelow_direct _ _ _].
    destruct (add_cons_inserted_bounds m i j d) as [Hfirst Hsecond].
    assert (Hedge1 : RelationalPathBounds.below
      (entry (fw direct) i j) (Some d)).
    { eapply RelationalPathBounds.below_trans;
        [apply Hbelow_direct|exact Hfirst]. }
    assert (Hedge2 : RelationalPathBounds.below
      (entry (fw direct) (flip j) (flip i)) (Some d)).
    { eapply RelationalPathBounds.below_trans;
        [apply Hbelow_direct|exact Hsecond]. }
    pose proof (closed_below_edge_extension (entry (fw direct))
      (entry seed) i j d Hclosed Hseed Hedge1) as Hone.
    pose proof (closed_below_edge_extension (entry (fw direct))
      (RelationalPathBounds.edge_extension (entry seed) i j d)
      (flip j) (flip i) d Hclosed Hone Hedge2 a b) as Htwo.
    pose proof (fw_mixed_cycle m i j d Hwf Hscan) as Hmixed.
    change (RelationalPathBounds.below (Some 0%Z)
      (twin_path d (Some 0%Z) (entry seed j (flip j))
        (entry seed (flip i) i))) in Hmixed.
    rewrite (incremental_sequential_extension seed i j d Hmixed a b).
    exact Htwo.
  Qed.

  Lemma matrix_ok_of_all_nonnegative : forall m,
    (forall k, nonnegative k m = true) -> matrix_ok m = true.
  Proof.
    intros m Hnonnegative. unfold matrix_ok.
    apply (fold_invariant _ _ (fun ok => ok = true)); [reflexivity|].
    intros ok k row Hok. rewrite Hok, Hnonnegative. reflexivity.
  Qed.

  (** A successful full Floyd scan makes the incremental scan pass. *)
  Lemma full_scan_implies_incremental_scan : forall m i j d, dbm_wf m ->
    let direct := add_cons i j d m in
    let seed := add_cons j j 0%Z (add_cons i i 0%Z m) in
    forallb (fun k => nonnegative k (fw direct)) (keys direct) = true ->
    matrix_ok (increment_matrix i j d seed) = true.
  Proof.
    intros m i j d Hwf. cbn beta iota zeta.
    set (direct := add_cons i j d m).
    set (seed := add_cons j j 0%Z (add_cons i i 0%Z m)).
    set (next := increment_matrix i j d seed). intro Hscan.
    assert (Hwfdirect : dbm_wf direct).
    { unfold direct. now apply add_cons_wf. }
    pose proof (proj1 (fw_closed_success direct Hwfdirect Hscan)) as Hzero.
    apply matrix_ok_of_all_nonnegative. intro k. unfold nonnegative.
    destruct (entry next k k) as [value|] eqn:Hentry; [|reflexivity].
    assert (Hsupport : In (K.encode k) (support (fw direct))).
    { apply (proj2 (fw_support direct (K.encode k))).
      apply (proj2 (direct_seed_support m i j d (K.encode k))).
      apply (proj1 (support_increment i j d seed (K.encode k))).
      eapply entry_source_support. exact Hentry. }
    pose proof (Hzero k Hsupport) as Hdiag.
    pose proof (fw_below_candidate_on_full_scan m i j d Hwf Hscan k k)
      as Hbound.
    change (RelationalPathBounds.below
      (entry (fw direct) k k) (entry next k k)) in Hbound.
    rewrite Hdiag, Hentry in Hbound.
    apply Z.leb_le. exact Hbound.
  Qed.

  (** Tightening and strengthening respect pointwise matrix equality. *)
  Lemma final_pass_entry_ext : forall a b, dbm_wf a -> dbm_wf b ->
    (forall i j, entry a i j = entry b i j) ->
    forall i j,
      entry (strengthen (tighten a)) i j =
      entry (strengthen (tighten b)) i j.
  Proof.
    intros a b Hwa Hwb Hentry.
    assert (Htight : forall i j,
      entry (tighten a) i j = entry (tighten b) i j).
    { intros i j. rewrite (entry_tighten_exact a Hwa),
        (entry_tighten_exact b Hwb). now rewrite Hentry. }
    intros i j.
    rewrite (entry_strengthen_exact (tighten a) (wf_tighten a Hwa)),
      (entry_strengthen_exact (tighten b) (wf_tighten b Hwb)).
    now rewrite (Htight i (flip i)), (Htight i j),
      (Htight (flip j) j).
  Qed.

  (** Pointwise equality aligns the sparse and pivot-list diagonal scans. *)
  Lemma matrix_ok_forallb_equal : forall ma mb direct, dbm_wf ma ->
    dbm_wf direct ->
    (forall i j, entry ma i j = entry mb i j) ->
    (forall p, In p (support mb) -> In p (support direct)) ->
    matrix_ok ma = forallb (fun k => nonnegative k mb) (keys direct).
  Proof.
    intros ma mb direct Hwfma Hwfdirect Heq Hsupport.
    destruct (matrix_ok ma) eqn:Hma;
      destruct (forallb (fun k => nonnegative k mb) (keys direct))
        eqn:Hmb; try reflexivity.
    - exfalso. apply Bool.not_true_iff_false in Hmb.
      apply Hmb. apply forallb_forall. intros k Hkey.
      unfold nonnegative. destruct (entry ma k k) as [z|] eqn:Hentry;
        [|rewrite <- (Heq k k); now rewrite Hentry].
      assert (Hrow : exists row, M.get k ma = Some row).
      { unfold entry in Hentry. destruct (M.get k ma) as [row|] eqn:Hget;
          [now exists row|discriminate]. }
      destruct Hrow as [row Hrow].
      pose proof (matrix_ok_row ma k row Hwfma Hma Hrow) as Hcheck.
      unfold nonnegative in Hcheck. rewrite Hentry in Hcheck.
      rewrite <- (Heq k k). now rewrite Hentry.
    - exfalso. apply Bool.not_true_iff_false in Hma.
      apply Hma. apply matrix_ok_of_all_nonnegative. intro k.
      unfold nonnegative. destruct (entry ma k k) as [z|] eqn:Hentry;
        [|reflexivity].
      assert (Hmbentry : entry mb k k = Some z).
      { now rewrite <- (Heq k k). }
      assert (Hkey : In k (keys direct)).
      { apply keys_cover; [exact Hwfdirect|].
        apply Hsupport. eapply entry_source_support. exact Hmbentry. }
      rewrite forallb_forall in Hmb.
      pose proof (Hmb k Hkey) as Hcheck.
      unfold nonnegative in Hcheck. now rewrite Hmbentry in Hcheck.
  Qed.

  Lemma incr_close_eq : forall m i j d, dbm_wf m -> tightly_closed m ->
    same_entries (incr_close i j d m) (tclose (add_cons i j d m)).
  Proof.
    intros m i j d Hwf Htight.
    set (direct := add_cons i j d m).
    set (seed := add_cons j j 0%Z (add_cons i i 0%Z m)).
    set (next := increment_matrix i j d seed).
    set (full := fw direct).
    assert (Hwfdirect : dbm_wf direct).
    { unfold direct. now apply add_cons_wf. }
    assert (Hwfseed : dbm_wf seed).
    { unfold seed. apply add_cons_wf, add_cons_wf. exact Hwf. }
    assert (Hwfnext : dbm_wf next).
    { unfold next. now apply increment_wf. }
    assert (Hscan_eq : matrix_ok next =
      forallb (fun k => nonnegative k full) (keys direct)).
    { destruct (matrix_ok next) eqn:Hcandidate;
        destruct (forallb (fun k => nonnegative k full) (keys direct))
          eqn:Hfull; try reflexivity.
      - pose proof (incremental_candidate_fw_scan m i j d Hwf Htight
          Hcandidate) as Hscan.
        change (forallb (fun k => nonnegative k full) (keys direct) = true)
          in Hscan. congruence.
      - pose proof (full_scan_implies_incremental_scan m i j d Hwf Hfull)
          as Hscan.
        change (matrix_ok next = true) in Hscan. congruence. }
    unfold incr_close, tclose. rewrite pivot_keys_eq_keys.
    rewrite <- fw_keys.
    change (same_entries
      (if matrix_ok next then
        if matrix_ok (strengthen (tighten next))
          then Reached (strengthen (tighten next)) else Unreached
       else Unreached)
      (if forallb (fun k => nonnegative k full) (keys direct) then
        if forallb (fun k => nonnegative k (strengthen (tighten full)))
          (keys direct)
          then Reached (strengthen (tighten full)) else Unreached
       else Unreached)).
    rewrite Hscan_eq.
    destruct (forallb (fun k => nonnegative k full) (keys direct))
      eqn:Hfullscan; [|exact I].
    assert (Hcandidate : matrix_ok next = true).
    { exact Hscan_eq. }
    destruct (incremental_fw_equal m i j d Hwf Htight Hcandidate)
      as [_ Hentry].
    change (forall x y, entry next x y = entry full x y) in Hentry.
    pose proof (final_pass_entry_ext next full Hwfnext
      (wf_fw direct Hwfdirect) Hentry) as Hfinal.
    assert (Hcheck : matrix_ok (strengthen (tighten next)) =
      forallb (fun k => nonnegative k (strengthen (tighten full)))
        (keys direct)).
    { apply matrix_ok_forallb_equal.
      - apply wf_strengthen, wf_tighten. exact Hwfnext.
      - exact Hwfdirect.
      - exact Hfinal.
      - intros p Hp.
        apply (proj1 (fw_support direct p)).
        apply (proj1 (support_tighten (fw direct) p)).
        apply (proj1 (support_strengthen (tighten (fw direct)) p)).
        exact Hp. }
    rewrite Hcheck.
    destruct (forallb (fun k => nonnegative k (strengthen (tighten full)))
      (keys direct)); [exact Hfinal|exact I].
  Qed.

  (** A coherent triangle transports a unary half-bound across one edge. *)
  Lemma unary_half_transport : forall m, coherent m ->
    (forall i j k a z, entry m i k = Some a -> entry m k j = Some z ->
      exists d, entry m i j = Some d /\ (d <= a + z)%Z) ->
    forall i k a b c, entry m i k = Some a ->
      entry m k (flip k) = Some b -> entry m i (flip i) = Some c ->
      (Z.div2 c <= a + Z.div2 b)%Z.
  Proof.
    intros m Hcoh Htri i k a b c Hik Hkb Hic.
    destruct (Htri i (flip k) k a b Hik Hkb) as [d [Hikbar Hd]].
    assert (Hbar : entry m (flip k) (flip i) = Some a).
    { change (entry m (bar k) (bar i) = Some a).
      rewrite <- (Hcoh i k). exact Hik. }
    destruct (Htri i (flip i) (flip k) d a Hikbar Hbar)
      as [c' [Hic' Hc']].
    rewrite Hic in Hic'. inversion Hic'; subst c'.
    rewrite !Z.div2_div.
    pose proof (Z.div_mod c 2 ltac:(lia)) as Hcdiv.
    pose proof (Z.mod_pos_bound c 2 ltac:(lia)) as Hcrem.
    pose proof (Z.div_mod b 2 ltac:(lia)) as Hbdiv.
    pose proof (Z.mod_pos_bound b 2 ltac:(lia)) as Hbrem.
    lia.
  Qed.

  Definition half_unary (m : dbm) (i : K.t) : option Z :=
    option_map Z.div2 (entry m i (flip i)).

  Definition strong_view (m : dbm) (i j : K.t) : option Z :=
    RelationalPathBounds.minimum (entry m i j)
      (RelationalPathBounds.plus (half_unary m i) (half_unary m (flip j))).

  Lemma even_half_sum : forall a b,
    Z.div2 (even_bound a + even_bound b) = (Z.div2 a + Z.div2 b)%Z.
  Proof.
    intros a b. unfold even_bound. rewrite Z.div2_div.
    replace (2 * Z.div2 a + 2 * Z.div2 b)%Z with
      ((Z.div2 a + Z.div2 b) * 2)%Z by ring.
    now rewrite Z.div_mul by lia.
  Qed.

  (** Tightening and strengthening implement the unary-half minimum. *)
  Lemma strengthen_tighten_view : forall m, dbm_wf m -> forall i j,
    entry (strengthen (tighten m)) i j = strong_view m i j.
  Proof.
    intros m Hwf i j.
    destruct (K.eqb_spec j (flip i)) as [Heq|Hne].
    - subst j. rewrite entry_strengthen_unary by (apply wf_tighten; exact Hwf).
      rewrite entry_tighten_unary_option by exact Hwf.
      unfold strong_view, half_unary. rewrite flip_involutive.
      destruct (entry m i (flip i)) as [a|] eqn:Hunary;
        cbn [option_map RelationalPathBounds.plus RelationalPathBounds.minimum];
        [|reflexivity].
      unfold even_bound.
      rewrite Z.div2_div.
      pose proof (Z.div_mod a 2 ltac:(lia)) as Hdiv.
      pose proof (Z.mod_pos_bound a 2 ltac:(lia)) as Hmod.
      rewrite Z.min_r by lia. f_equal. lia.
    - rewrite entry_strengthen_exact by (apply wf_tighten; exact Hwf).
      rewrite entry_tighten_unary_option by exact Hwf.
      pose proof (entry_tighten_unary_option m Hwf (flip j)) as Hright.
      rewrite flip_involutive in Hright. rewrite Hright.
      rewrite entry_tighten_other by exact Hne.
      unfold strong_view, half_unary. rewrite flip_involutive.
      destruct (entry m i (flip i)) as [a|],
        (entry m (flip j) j) as [b|], (entry m i j) as [old|];
        cbn [option_map RelationalPathBounds.plus RelationalPathBounds.minimum
          strengthen_bound lower_bound]; try reflexivity.
      + rewrite even_half_sum. f_equal. apply Z.min_comm.
      + now rewrite even_half_sum.
  Qed.

  Lemma half_unary_transport : forall m, coherent m ->
    (forall i j k a z, entry m i k = Some a -> entry m k j = Some z ->
      exists d, entry m i j = Some d /\ (d <= a + z)%Z) ->
    forall i k, RelationalPathBounds.below (half_unary m i)
      (RelationalPathBounds.plus (entry m i k) (half_unary m k)).
  Proof.
    intros m Hcoh Htri i k. unfold half_unary.
    destruct (entry m i k) as [a|] eqn:Hik;
      destruct (entry m k (flip k)) as [b|] eqn:Hkb;
      cbn [option_map RelationalPathBounds.plus RelationalPathBounds.below];
      try (destruct (entry m i (flip i)); exact I).
    destruct (Htri i (flip k) k a b Hik Hkb) as [d [Hikbar Hd]].
    assert (Hbar : entry m (flip k) (flip i) = Some a).
    { change (entry m (bar k) (bar i) = Some a).
      rewrite <- (Hcoh i k). exact Hik. }
    destruct (Htri i (flip i) (flip k) d a Hikbar Hbar)
      as [c [Hic Hc]].
    rewrite Hic. cbn [option_map RelationalPathBounds.below].
    exact (unary_half_transport m Hcoh Htri i k a b c Hik Hkb Hic).
  Qed.

  (** Unary strengthening preserves every triangle when opposite halves are consistent. *)
  Lemma strong_view_triangle : forall m, coherent m ->
    (forall k, RelationalPathBounds.closed_at (entry m) k) ->
    (forall i k, RelationalPathBounds.below (half_unary m i)
      (RelationalPathBounds.plus (entry m i k) (half_unary m k))) ->
    (forall k, RelationalPathBounds.below (Some 0%Z)
      (RelationalPathBounds.plus (half_unary m (flip k)) (half_unary m k))) ->
    forall i j k, RelationalPathBounds.below (strong_view m i j)
      (RelationalPathBounds.plus (strong_view m i k) (strong_view m k j)).
  Proof.
    intros m Hcoh Hclosed Htransport Hpair i j k.
    unfold strong_view.
    rewrite RelationalPathBounds.plus_minimum_l.
    rewrite !RelationalPathBounds.plus_minimum_r.
    apply RelationalPathBounds.minimum_glb. split;
      apply RelationalPathBounds.minimum_glb; split.
    - eapply RelationalPathBounds.below_trans.
      + apply RelationalPathBounds.minimum_l.
      + apply Hclosed.
    - eapply RelationalPathBounds.below_trans.
      + apply RelationalPathBounds.minimum_r.
      + pose proof (Htransport (flip j) (flip k)) as Hstep.
        assert (Hmirror : entry m (flip j) (flip k) = entry m k j).
        { change (entry m (bar j) (bar k) = entry m k j).
          symmetry. apply Hcoh. }
        rewrite Hmirror in Hstep.
        eapply RelationalPathBounds.below_trans.
        * apply RelationalPathBounds.plus_mono;
            [apply RelationalPathBounds.below_refl|exact Hstep].
        * rewrite !RelationalPathBounds.plus_assoc.
          rewrite (RelationalPathBounds.plus_comm (entry m k j)
            (half_unary m (flip k))).
          apply RelationalPathBounds.below_refl.
    - eapply RelationalPathBounds.below_trans.
      + apply RelationalPathBounds.minimum_r.
      + eapply RelationalPathBounds.below_trans.
        * apply RelationalPathBounds.plus_mono;
            [apply Htransport|apply RelationalPathBounds.below_refl].
        * rewrite RelationalPathBounds.plus_assoc.
          apply RelationalPathBounds.below_refl.
    - eapply RelationalPathBounds.below_trans.
      + apply RelationalPathBounds.minimum_r.
      + eapply RelationalPathBounds.below_trans.
        * replace (RelationalPathBounds.plus (half_unary m i)
            (half_unary m (flip j))) with
            (RelationalPathBounds.plus
              (RelationalPathBounds.plus (half_unary m i) (Some 0%Z))
              (half_unary m (flip j)))
            by (rewrite RelationalPathBounds.plus_zero_r; reflexivity).
          apply RelationalPathBounds.plus_mono;
            [apply RelationalPathBounds.plus_mono;
              [apply RelationalPathBounds.below_refl|apply Hpair]|
             apply RelationalPathBounds.below_refl].
        * rewrite !RelationalPathBounds.plus_assoc.
          rewrite (RelationalPathBounds.plus_comm (half_unary m k)
            (half_unary m (flip j))).
          apply RelationalPathBounds.below_refl.
  Qed.

  (** A successful tight closure is coherent after both numeric passes. *)
  Lemma coherent_tclose_reached : forall m m', dbm_wf m -> coherent m -> bar_closed m ->
    tclose m = Reached m' -> coherent m'.
  Proof.
    intros m m' Hwf Hcoh Hbar Hresult.
    unfold tclose in Hresult. rewrite pivot_keys_eq_keys in Hresult.
    rewrite <- fw_keys in Hresult.
    destruct (forallb (fun k => nonnegative k (fw m)) (keys m)) eqn:Hscan;
      [|discriminate].
    destruct (forallb (fun k => nonnegative k (strengthen (tighten (fw m))))
      (keys m)); [|discriminate].
    inversion Hresult; subst m'.
    apply coherent_strengthen, coherent_tighten.
    now apply coherent_fw_success.
  Qed.

  (** Successful closure leaves every stored unary bound even. *)
  Lemma tclose_unary_even : forall m m', dbm_wf m ->
    tclose m = Reached m' ->
    forall i d, entry m' i (flip i) = Some d -> (d mod 2 = 0)%Z.
  Proof.
    intros m m' Hwf Hresult i d Hentry.
    unfold tclose in Hresult. rewrite pivot_keys_eq_keys in Hresult.
    rewrite <- fw_keys in Hresult.
    destruct (forallb (fun k => nonnegative k (fw m)) (keys m));
      [|discriminate].
    destruct (forallb (fun k => nonnegative k (strengthen (tighten (fw m))))
      (keys m)); [|discriminate].
    inversion Hresult; subst m'.
    rewrite entry_strengthen_unary in Hentry.
    - eapply tighten_unary_even; [apply wf_fw; exact Hwf|exact Hentry].
    - apply wf_tighten, wf_fw. exact Hwf.
  Qed.

  (** Successful final diagonal checking leaves every supported diagonal zero. *)
  Lemma tclose_zero_diag : forall m m', dbm_wf m ->
    tclose m = Reached m' ->
    forall i, In (K.encode i) (support m') -> entry m' i i = Some 0%Z.
  Proof.
    intros m m' Hwf Hresult i Hsupport.
    unfold tclose in Hresult. rewrite pivot_keys_eq_keys in Hresult.
    rewrite <- fw_keys in Hresult.
    destruct (forallb (fun k => nonnegative k (fw m)) (keys m)) eqn:Hfirst;
      [|discriminate].
    destruct (forallb (fun k => nonnegative k (strengthen (tighten (fw m))))
      (keys m)) eqn:Hsecond; [|discriminate].
    inversion Hresult; subst m'.
    assert (Hsource : In (K.encode i) (support (fw m))).
    { apply (proj1 (support_tighten (fw m) (K.encode i))).
      apply (proj1 (support_strengthen (tighten (fw m)) (K.encode i))).
      exact Hsupport. }
    pose proof (proj1 (fw_closed_success m Hwf Hfirst) i Hsource) as Hzero.
    assert (Hne : i <> flip i).
    { intros Heq. destruct i as [x s]. destruct s; discriminate. }
    assert (Htight : entry (tighten (fw m)) i i = Some 0%Z).
    { rewrite entry_tighten_other by exact Hne. exact Hzero. }
    pose proof (strengthen_below_old (tighten (fw m))
      (wf_tighten (fw m) (wf_fw m Hwf)) i i) as Hbelow.
    rewrite Htight in Hbelow.
    destruct (RelationalPathBounds.below_finite _ _ Hbelow)
      as [d [Hd Hle]].
    rewrite forallb_forall in Hsecond.
    assert (Hkey : In i (keys m)).
    { apply (proj2 (keys_support_iff m i Hwf)).
      apply (proj1 (fw_support m (K.encode i))). exact Hsource. }
    pose proof (Hsecond i Hkey) as Hnonnegative.
    unfold nonnegative in Hnonnegative. rewrite Hd in Hnonnegative.
    apply Z.leb_le in Hnonnegative. assert (d = 0)%Z by lia.
    now subst d.
  Qed.

  (** A zero output diagonal rules out a negative tightened unary pair. *)
  Lemma tclose_pair_nonnegative : forall m m', dbm_wf m ->
    tclose m = Reached m' ->
    forall i a z,
      entry (tighten (fw m)) i (flip i) = Some a ->
      entry (tighten (fw m)) (flip i) i = Some z -> (0 <= a + z)%Z.
  Proof.
    intros m m' Hwf Hresult i a z Hleft Hright.
    pose proof Hresult as Hresult0.
    unfold tclose in Hresult. rewrite pivot_keys_eq_keys in Hresult.
    rewrite <- fw_keys in Hresult.
    destruct (forallb (fun k => nonnegative k (fw m)) (keys m));
      [|discriminate].
    destruct (forallb (fun k => nonnegative k (strengthen (tighten (fw m))))
      (keys m)); [|discriminate].
    inversion Hresult; subst m'.
    assert (Hsupport : In (K.encode i) (support (strengthen (tighten (fw m))))).
    { apply (proj2 (support_strengthen (tighten (fw m)) (K.encode i))).
      eapply entry_source_support. exact Hleft. }
    pose proof (tclose_zero_diag m (strengthen (tighten (fw m))) Hwf Hresult0
      i Hsupport) as Hdiag.
    rewrite entry_strengthen_exact in Hdiag by (apply wf_tighten, wf_fw; exact Hwf).
    rewrite Hleft, Hright in Hdiag.
    cbn [strengthen_bound lower_bound] in Hdiag.
    destruct (entry (tighten (fw m)) i i) as [old|] eqn:Hold;
      inversion Hdiag; subst; clear Hdiag.
    - pose proof (Z.le_min_l (Z.div2 (a + z)) old) as Hmin.
      rewrite Z.div2_div in *.
      pose proof (Z.div_mod (a + z) 2 ltac:(lia)) as Hdiv.
      pose proof (Z.mod_pos_bound (a + z) 2 ltac:(lia)) as Hmod.
      lia.
    - rewrite Z.div2_div in *.
      pose proof (Z.div_mod (a + z) 2 ltac:(lia)) as Hdiv.
      pose proof (Z.mod_pos_bound (a + z) 2 ltac:(lia)) as Hmod.
      lia.
  Qed.

  Lemma tclose_half_pair : forall m m', dbm_wf m ->
    tclose m = Reached m' ->
    forall k, RelationalPathBounds.below (Some 0%Z)
      (RelationalPathBounds.plus (half_unary (fw m) (flip k)) (half_unary (fw m) k)).
  Proof.
    intros m m' Hwf Hresult k. unfold half_unary.
    rewrite flip_involutive.
    destruct (entry (fw m) (flip k) k) as [a|] eqn:Ha;
      destruct (entry (fw m) k (flip k)) as [b|] eqn:Hb;
      cbn [option_map RelationalPathBounds.plus RelationalPathBounds.below];
      try exact I.
    assert (Hfirst : entry (tighten (fw m)) k (flip k) = Some (even_bound b)).
    { rewrite entry_tighten_unary_option by (apply wf_fw; exact Hwf).
      now rewrite Hb. }
    assert (Hsecond : entry (tighten (fw m)) (flip k) k = Some (even_bound a)).
    { pose proof (entry_tighten_unary_option (fw m) (wf_fw m Hwf) (flip k)) as Hopt.
      rewrite flip_involutive, Ha in Hopt. exact Hopt. }
    pose proof (tclose_pair_nonnegative m m' Hwf Hresult k
      (even_bound b) (even_bound a) Hfirst Hsecond) as Hpair.
    unfold even_bound in Hpair.
    cbn [RelationalPathBounds.below]. lia.
  Qed.

  (** Successful tight closure preserves every triangle inequality. *)
  Lemma tclose_triangle : forall m m', dbm_wf m -> coherent m -> bar_closed m ->
    tclose m = Reached m' ->
    forall i j k a z, entry m' i k = Some a -> entry m' k j = Some z ->
      exists d, entry m' i j = Some d /\ (d <= a + z)%Z.
  Proof.
    intros m m' Hwf Hcoh Hbar Hresult i j k a z Hik Hkj.
    pose proof Hresult as Hresult0.
    unfold tclose in Hresult. rewrite pivot_keys_eq_keys in Hresult.
    rewrite <- fw_keys in Hresult.
    destruct (forallb (fun p => nonnegative p (fw m)) (keys m)) eqn:Hfirst;
      [|discriminate].
    destruct (forallb (fun p => nonnegative p (strengthen (tighten (fw m))))
      (keys m)); [|discriminate].
    inversion Hresult; subst m'.
    pose proof (coherent_fw_success m Hwf Hcoh Hbar Hfirst) as Hcoh_fw.
    pose proof (proj2 (fw_closed_success m Hwf Hfirst)) as Htri_fw.
    pose proof (strong_view_triangle (fw m) Hcoh_fw
      (fw_closed_at_success m Hwf Hfirst)
      (half_unary_transport (fw m) Hcoh_fw Htri_fw)
      (tclose_half_pair m (strengthen (tighten (fw m))) Hwf Hresult0)
      i j k) as Hbound.
    rewrite (strengthen_tighten_view (fw m) (wf_fw m Hwf)) in Hik, Hkj |- *.
    rewrite Hik, Hkj in Hbound. cbn [RelationalPathBounds.plus] in Hbound.
    destruct (RelationalPathBounds.below_finite _ _ Hbound)
      as [d [Hd Hle]]. exists d. now split.
  Qed.

  Lemma tclose_strong_clause : forall m m', dbm_wf m ->
    tclose m = Reached m' ->
    forall i j a z, entry m' i (flip i) = Some a ->
      entry m' (flip j) j = Some z ->
      exists d, entry m' i j = Some d /\ (2 * d <= a + z)%Z.
  Proof.
    intros m m' Hwf Hresult i j a z Hleft Hright.
    unfold tclose in Hresult. rewrite pivot_keys_eq_keys in Hresult.
    rewrite <- fw_keys in Hresult.
    destruct (forallb (fun k => nonnegative k (fw m)) (keys m));
      [|discriminate].
    destruct (forallb (fun k => nonnegative k (strengthen (tighten (fw m))))
      (keys m)); [|discriminate].
    inversion Hresult; subst m'.
    eapply strengthen_strong_clause;
      [apply wf_tighten, wf_fw; exact Hwf|exact Hleft|exact Hright].
  Qed.

  (** A successful integer closure is coherent, closed, strong and unary-even. *)
  Lemma tclose_tight : forall m m', dbm_wf m -> coherent m -> bar_closed m ->
    tclose m = Reached m' -> tightly_closed m'.
  Proof.
    intros m m' Hwf Hcoh Hbar Hresult.
    unfold tightly_closed, strongly_closed. split.
    - split.
      + eapply coherent_tclose_reached; eauto.
      + split.
        * eapply tclose_zero_diag; eauto.
        * split.
          -- eapply tclose_triangle; eauto.
          -- eapply tclose_strong_clause; eauto.
    - eapply tclose_unary_even; eauto.
  Qed.

  Lemma coh_tclose : forall m, dbm_wf m -> coherent m -> bar_closed m -> coh (tclose m).
  Proof.
    intros m Hwf Hcoh Hbar.
    destruct (tclose m) as [|m'] eqn:Hresult; [exact I|].
    exact (proj1 (proj1 (tclose_tight m m' Hwf Hcoh Hbar Hresult))).
  Qed.

  (** Rounding a unary entry down changes its absolute value by at most one. *)
  Lemma even_bound_abs : forall d,
    Z.abs_nat (even_bound d) <= Z.abs_nat d + 1.
  Proof.
    intro d.
    replace (even_bound d) with (d + - (d mod 2))%Z.
    - eapply Nat.le_trans; [apply rel_abs_add|].
      pose proof (Z.mod_pos_bound d 2 ltac:(lia)) as Hrem.
      assert (d mod 2 = 0 \/ d mod 2 = 1)%Z by lia.
      destruct H as [Hzero|Hone]; rewrite ?Hzero, ?Hone;
        cbn [Z.abs_nat]; lia.
    - unfold even_bound. rewrite Z.div2_div.
      pose proof (Z.div_mod d 2 ltac:(lia)) as Hdiv. lia.
  Qed.

  (** A rounded entry stays within one unit of the input magnitude bound. *)
  Lemma tighten_entry_abs : forall m upper, dbm_wf m ->
    (forall i j d, entry m i j = Some d -> Z.abs_nat d <= upper) ->
    forall i j d, entry (tighten m) i j = Some d -> Z.abs_nat d <= upper + 1.
  Proof.
    intros m upper Hwf Hbound i j d Hentry.
    rewrite entry_tighten_exact in Hentry by exact Hwf.
    destruct (K.eqb j (flip i)) eqn:Hflip.
    - destruct (entry m i j) as [old|] eqn:Hold; [|discriminate].
      cbn [option_map] in Hentry. injection Hentry as <-.
      pose proof (even_bound_abs old) as Hround.
      pose proof (Hbound i j old Hold) as Hraw. lia.
    - pose proof (Hbound i j d Hentry). lia.
  Qed.

  (** The support bound has enough room for one unary-rounding unit. *)
  Lemma support_power_margin : forall m,
    supp m * (2 ^ ell m - 1) + 1 < 2 ^ (ell m + Nat.log2 (supp m) + 1).
  Proof.
    intro m. set (s := supp m). set (p := 2 ^ ell m).
    assert (Hp : 0 < p).
    { unfold p. pose proof (Nat.pow_nonzero 2 (ell m) ltac:(lia)). lia. }
    assert (Hs : s < 2 ^ (Nat.log2 s + 1)).
    { destruct s as [|s].
      - pose proof (Nat.pow_nonzero 2 (Nat.log2 0 + 1) ltac:(lia)) as Hpower.
        lia.
      - pose proof (Nat.log2_spec (S s) ltac:(lia)) as [_ Hupper].
        replace (Nat.log2 (S s) + 1) with (S (Nat.log2 (S s))) by lia.
        exact Hupper. }
    rewrite <- Nat.add_assoc.
    rewrite (Nat.pow_add_r 2 (ell m) (Nat.log2 s + 1)). fold p.
    set (q := 2 ^ (Nat.log2 s + 1)) in *.
    assert (Hq : 2 <= q).
    { unfold q. replace (Nat.log2 s + 1) with (S (Nat.log2 s)) by lia.
      rewrite Nat.pow_succ_r by lia.
      pose proof (Nat.pow_nonzero 2 (Nat.log2 s) ltac:(lia)). nia. }
    assert (Hsub : p - 1 + 1 = p) by lia.
    destruct s as [|s].
    - nia.
    - assert (Hprod : (S s + 1) * p <= q * p).
      { apply Nat.mul_le_mono_r. lia. }
      assert (Hleft : S s * (p - 1) + 1 < (S s + 1) * p) by nia.
      nia.
  Qed.

  (** Successful integer closure fits the original support-sensitive bit budget. *)
  Lemma bits_tclose_le : forall m m', dbm_wf m -> tclose m = Reached m' ->
    ell m' <= ell m + Nat.log2 (supp m) + 1.
  Proof.
    intros m m' Hwf Hresult.
    unfold tclose in Hresult. rewrite pivot_keys_eq_keys in Hresult.
    rewrite <- fw_keys in Hresult.
    destruct (forallb (fun k => nonnegative k (fw m)) (keys m)) eqn:Hscan;
      [|discriminate].
    destruct (forallb (fun k => nonnegative k (strengthen (tighten (fw m))))
      (keys m)); [|discriminate].
    injection Hresult as <-.
    eapply Nat.le_trans; [apply bits_strengthen_le|].
    apply ell_bound. intros p q d Hraw.
    destruct (wf_raw_entry_keys (tighten (fw m)) p q d
      (wf_tighten (fw m) (wf_fw m Hwf)) Hraw) as [i [j [_ [_ Hentry]]]].
    apply zbits_least.
    eapply Nat.le_lt_trans; [|apply support_power_margin].
    eapply tighten_entry_abs; [apply wf_fw; exact Hwf| |exact Hentry].
    intros a b z Hz.
    eapply path_invariant_entry_abs;
      [apply fw_success_path_invariant; exact Hwf || exact Hscan|exact Hz].
  Qed.

  (** Original and final key lists cover the same supported vertices. *)
  Lemma keys_fw_membership : forall m k, dbm_wf m ->
    (In k (keys m) <-> In k (keys (fw m))).
  Proof.
    intros m k Hwf. rewrite (keys_support_iff m k Hwf).
    rewrite (keys_support_iff (fw m) k (wf_fw m Hwf)).
    symmetry. apply fw_support.
  Qed.

  (** Diagonal checking is independent of the order of the complete pivot lists. *)
  Lemma original_scan_diag_ok : forall m, dbm_wf m ->
    forallb (fun k => nonnegative k (fw m)) (keys m) = diag_ok (fw m).
  Proof.
    intros m Hwf. unfold diag_ok.
    change (forallb (fun k => nonnegative k (fw m)) (keys m) =
      forallb (fun k => nonnegative k (fw m)) (keys (fw m))).
    apply Bool.eq_true_iff_eq. rewrite !forallb_forall. split.
    - intros Hscan k Hkey. apply Hscan. now apply (proj2 (keys_fw_membership m k Hwf)).
    - intros Hscan k Hkey. apply Hscan. now apply (proj1 (keys_fw_membership m k Hwf)).
  Qed.

  (** The trace stops at the same negative diagonal as the executable pivot loop. *)
  Lemma fw_trace_nonnegative : forall k ks m,
    fw_trace (k :: ks) m = (k, m) ::
      if nonnegative k (fw_round k m) then fw_trace ks (fw_round k m) else nil.
  Proof.
    intros k ks m. cbn [fw_trace]. unfold nonnegative.
    destruct (entry (fw_round k m) k k) as [z|]; [|reflexivity].
    destruct (z <? 0)%Z eqn:Hneg; destruct (0 <=? z)%Z eqn:Hnonneg;
      try reflexivity.
    - apply Z.ltb_lt in Hneg. apply Z.leb_le in Hnonneg. lia.
    - apply Z.ltb_ge in Hneg. apply Z.leb_gt in Hnonneg. lia.
  Qed.

  (** A nonempty closure run returns the result of one recorded round. *)
  Lemma fw_pivots_last : forall ks m,
    fw_pivots ks m = m \/ exists k a,
      In (k, a) (fw_trace ks m) /\ fw_pivots ks m = fw_round k a.
  Proof.
    induction ks as [|k ks IH]; intro m; [now left|].
    right. cbn [fw_pivots]. rewrite fw_trace_nonnegative.
    destruct (nonnegative k (fw_round k m)) eqn:Hnext.
    - destruct (IH (fw_round k m)) as [Hsame|[q [a [Hin Hlast]]]].
      + exists k, m. split; [now left|exact Hsame].
      + exists q, a. split; [now right|exact Hlast].
    - exists k, m. split; [now left|reflexivity].
  Qed.

  (** The returned matrix adds at most one round to the checked trace allowance. *)
  Lemma fw_bits : forall m, dbm_wf m ->
    ell (fw m) <= ell m + Nat.log2 (supp m) + 2.
  Proof.
    intros m Hwf. rewrite fw_keys.
    destruct (fw_pivots_last (keys m) m) as [Hsame|[k [a [Hin Hlast]]]].
    - rewrite Hsame. lia.
    - rewrite Hlast. pose proof (bits_fw_round_step k a) as Hround.
      pose proof (bits_fw_trace_le (keys m) m k a Hwf Hin) as Htrace. lia.
  Qed.

  (** Tight closure pays two bounded diagonal scans beyond its numeric stages. *)
  Lemma T_tclose_overhead : forall m overhead, dbm_wf m ->
    (forall next,
      (List.T_forallb (fun k => nonnegative k next) (fun k => 1 + T_nonnegative k next)
        (keys m) <= overhead)%N) ->
    (T_tclose m <= T_fw m + 2 * overhead + 8 +
      if diag_ok (fw m) then T_tighten (fw m) + T_strengthen (tighten (fw m)) else 0)%N.
  Proof.
    intros m overhead Hwf Hscan.
    pose proof (Hscan (fw m)) as Hfirst.
    pose proof (Hscan (strengthen (tighten (fw m)))) as Hlast.
    unfold T_tclose, T_fw. cbn beta iota zeta.
    rewrite pivot_keys_eq_keys, <- fw_keys.
    rewrite original_scan_diag_ok by exact Hwf.
    destruct (diag_ok (fw m)); cbn beta iota zeta; time_simpl; lia.
  Qed.
  (** A fresh lookup gains exactly one stored code when inserted. *)
  Lemma fresh_set_codes_length : forall (A : Type) k (a : A) m,
    M.get k m = None -> length (M.codes (M.set k a m)) = S (length (M.codes m)).
  Proof.
    intros A k a m Hnone. rewrite M.get_find in Hnone.
    assert (Hnew : incl (M.codes (M.set k a m)) (K.encode k :: M.codes m)).
    { intros p Hp. apply M.codes_spec in Hp. rewrite M.find_set in Hp.
      destruct (Pos.eqb p (K.encode k)) eqn:Hkey.
      - apply Pos.eqb_eq in Hkey. subst p. now left.
      - right. now apply M.codes_spec. }
    assert (Hold : incl (K.encode k :: M.codes m) (M.codes (M.set k a m))).
    { intros p [Hp|Hp]; apply M.codes_spec; rewrite M.find_set.
      - subst p. rewrite Pos.eqb_refl. discriminate.
      - apply M.codes_spec in Hp. destruct (Pos.eqb p (K.encode k)); congruence. }
    assert (Hnodup : NoDup (K.encode k :: M.codes m)).
    { constructor; [|apply M.codes_nodup].
      intro Hin. apply M.codes_spec in Hin. contradiction. }
    pose proof (NoDup_incl_length (M.codes_nodup A (M.set k a m)) Hnew).
    pose proof (NoDup_incl_length Hnodup Hold). cbn in *. lia.
  Qed.

  (** Pairing a fold with its running clock does not change the computed accumulator. *)
  Lemma fold_clock_value : forall (A B : Type) (step : B -> A -> B)
      (clock : B -> A -> N) xs acc spent,
    fst (fold_left (fun bw x => (step (fst bw) x, (snd bw + clock (fst bw) x)%N))
      xs (acc, spent)) = fold_left step xs acc.
  Proof.
    intros A B step clock xs. induction xs as [|x xs IH]; intros acc spent;
      cbn [fold_left fst snd]; [reflexivity|apply IH].
  Qed.

  (** A potential increase pays for every costly successful insertion exactly once. *)
  Lemma fold_potential_time : forall (A B : Type) (step : B -> A -> B)
      (clock : B -> A -> N) (potential : B -> N) (weight : A -> N) xs acc spent,
    (forall state x, (clock state x + potential state <=
      weight x + potential (step state x))%N) ->
    let done := fold_left
      (fun bw x => (step (fst bw) x, (snd bw + clock (fst bw) x)%N)) xs (acc, spent) in
    (snd done + potential acc <=
      spent + fold_right N.add 0%N (map weight xs) + potential (fst done))%N.
  Proof.
    intros A B step clock potential weight xs.
    induction xs as [|x xs IH]; intros acc spent Hstep;
      cbn [fold_left map fold_right fst snd].
    - lia.
    - pose proof (IH (step acc x) (spent + clock acc x)%N Hstep) as Hrest.
      pose proof (Hstep acc x) as Hone. cbn [fst snd] in Hrest. lia.
  Qed.

  (** Every cached tightening row was looked up successfully in the original matrix. *)
  Definition tightened_sources (m changed : dbm) : Prop :=
    forall p, M.find p changed <> None -> M.find p m <> None.

  Lemma tighten_row_sources : forall m changed k ignored,
    tightened_sources m changed -> tightened_sources m (tighten_row m changed k ignored).
  Proof.
    intros m changed k ignored Hsources. unfold tighten_row.
    destruct (M.get k changed); [exact Hsources|].
    destruct (M.get k m) as [row|] eqn:Hrow; [|exact Hsources].
    destruct (M.get (flip k) row); [|exact Hsources].
    intros p Hp. rewrite M.find_set in Hp.
    destruct (Pos.eqb p (K.encode k)) eqn:Hkey.
    - apply Pos.eqb_eq in Hkey. subst p. rewrite <- M.get_find, Hrow. discriminate.
    - now apply Hsources.
  Qed.

  Lemma collected_tighten_support : forall m p,
    In p (M.codes (M.fold (tighten_row m) m M.empty)) -> In p (support m).
  Proof.
    intros m p Hp. apply M.codes_spec in Hp.
    assert (Hsources : tightened_sources m (M.fold (tighten_row m) m M.empty)).
    { apply (fold_invariant _ _ (tightened_sources m)).
      - intros q Hq. rewrite M.find_empty in Hq. contradiction.
      - intros changed k ignored Hchanged. now apply tighten_row_sources. }
    apply support_find. left. now apply Hsources.
  Qed.

  Lemma T_even_bound_le : forall d,
    (T_even_bound d <= 32 * N.of_nat (Z.size_nat d + 1))%N.
  Proof.
    intro d. pose proof (zbits_div2 d). time_step.
  Qed.

  Local Definition tightening_charge (m changed : dbm) (k : K.t) : N :=
    match M.get k changed with
    | Some _ => 0%N
    | None =>
      match M.get k m with
      | Some row =>
        match M.get (flip k) row with
        | Some d => N.of_nat (Z.size_nat d + 1)
        | None => 0%N
        end
      | None => 0%N
      end
    end.

  (** Failed or repeated labels pay only lookup work; arithmetic is charged on fresh unaries. *)
  Lemma T_tighten_row_work : forall m changed k ignored,
    (T_tighten_row m changed k ignored <=
      64 * (M.c_map + 1) * N.of_nat (K.bits k + 1) +
        32 * tightening_charge m changed k)%N.
  Proof.
    intros m changed k ignored. pose proof (flip_bits k) as Hflip.
    unfold tightening_charge. destruct (M.get k changed) as [old|] eqn:Hcache.
    - unfold T_tighten_row. time_simpl. rewrite Hcache. time_simpl.
      time_pose. time_cbn_all. first [time_lin|nia].
    - destruct (M.get k m) as [row|] eqn:Hrow.
      + destruct (M.get (flip k) row) as [d|] eqn:Hbound.
        * unfold T_tighten_row. time_simpl. rewrite Hcache, Hrow, Hbound. time_simpl.
          time_pose. time_cbn_all. first [time_lin|nia].
        * unfold T_tighten_row. time_simpl. rewrite Hcache, Hrow, Hbound. time_simpl.
          time_pose. time_cbn_all. first [time_lin|nia].
      + unfold T_tighten_row. time_simpl. rewrite Hcache, Hrow. time_simpl.
        time_pose. time_cbn_all. first [time_lin|nia].
  Qed.

  Local Definition tightening_potential (m changed : dbm) : N :=
    (32 * N.of_nat (ell m + 1) * N.of_nat (length (M.codes changed)))%N.

  Lemma T_tighten_row_potential : forall m changed k ignored,
    (T_tighten_row m changed k ignored + tightening_potential m changed <=
      64 * (M.c_map + 1) * N.of_nat (K.bits k + 1) +
        tightening_potential m (tighten_row m changed k ignored))%N.
  Proof.
    intros m changed k ignored.
    pose proof (T_tighten_row_work m changed k ignored) as Hclock.
    unfold tightening_charge in Hclock. unfold tighten_row.
    destruct (M.get k changed) as [old|] eqn:Hcache; [lia|].
    destruct (M.get k m) as [row|] eqn:Hrow; [|lia].
    destruct (M.get (flip k) row) as [d|] eqn:Hbound; [|lia].
    assert (Hd : Z.size_nat d <= ell m).
    { eapply (ell_entry m (K.encode k) (K.encode (flip k)) d).
      unfold raw_entry. rewrite <- (M.get_find (M.t Z) k m), Hrow. cbn [row_of].
      now rewrite <- (M.get_find Z (flip k) row). }
    unfold tightening_potential.
    rewrite fresh_set_codes_length by exact Hcache.
    rewrite time_of_nat_succ, N.mul_add_distr_l.
    rewrite N.mul_1_r. nia.
  Qed.


  Local Definition tightening_work (m : dbm) : nat :=
    M.weight m + (supp m + 1) * (b m + ell m + 1) + 1.

  (** The deduplicating fold charges all labels, but arithmetic only at fresh supported codes. *)
  Lemma T_tighten_fold_small : forall m,
    (M.T_fold (tighten_row m) (fun changed k row => T_tighten_row m changed k row)
      m M.empty <= 128 * (M.c_map + 1) * (M.c_map + 1) *
        N.of_nat (tightening_work m))%N.
  Proof.
    intro m.
    pose proof (M.T_fold_sum_le (M.t Z) dbm (tighten_row m)
      (fun changed k row => T_tighten_row m changed k row) m M.empty) as Hclock.
    pose proof (fold_potential_time (K.t * M.t Z)%type dbm
      (fun changed ka => tighten_row m changed (fst ka) (snd ka))
      (fun changed ka => T_tighten_row m changed (fst ka) (snd ka))
      (tightening_potential m)
      (fun ka => (64 * (M.c_map + 1) * N.of_nat (K.bits (fst ka) + 1))%N)
      (M.elements m) M.empty 0%N
      ltac:(intros changed [k row]; apply T_tighten_row_potential)) as Hpotential.
    cbn zeta in Hpotential. rewrite fold_clock_value in Hpotential.
    rewrite <- (M.fold_spec (M.t Z) dbm (tighten_row m) m M.empty) in Hpotential.
    unfold tightening_potential in Hpotential. rewrite codes_empty in Hpotential.
    cbn [length] in Hpotential.
    rewrite ?N.mul_0_r, ?N.add_0_r, ?N.add_0_l in Hpotential.
    assert (Hlabels : (fold_right N.add 0%N
      (map (fun ka => (64 * (M.c_map + 1) * N.of_nat (K.bits (fst ka) + 1))%N)
        (M.elements m)) <= 64 * (M.c_map + 1) * N.of_nat (M.weight m))%N).
    { change (fold_right N.add 0%N
        (map (fun ka => (64 * (M.c_map + 1) * N.of_nat (K.bits (fst ka) + 1))%N)
          (M.elements m)) <= 64 * (M.c_map + 1) *
        N.of_nat (sum_weight (fun ka => (K.bits (fst ka) + 1)%nat) (M.elements m)))%N.
      apply time_sum_bound. intros ka Hka. apply N.le_refl. }
    pose proof (codes_support_length (M.t Z)
      (M.fold (tighten_row m) m M.empty) m (collected_tighten_support m)) as Hcount.
    assert (Houter : forall p, In p (M.codes m) -> In p (support m)).
    { intros p Hp. apply support_spec. now left. }
    pose proof (nodes_support (M.t Z) m m Houter) as Hnodes.
    set (work := N.of_nat (tightening_work m)).
    assert (Hlabels_work : (N.of_nat (M.weight m) <= work)%N).
    { unfold work, tightening_work. lia. }
    assert (Hnumeric_work :
      (N.of_nat (ell m + 1) * N.of_nat (supp m) <= work)%N).
    { rewrite <- Nat2N.inj_mul. unfold work. apply time_of_nat_le.
      unfold tightening_work. nia. }
    assert (Hnodes_work : (N.of_nat (M.nodes m + 1) <= work)%N).
    { unfold work. apply time_of_nat_le. unfold tightening_work. nia. }
    assert (Hlabels' : (fold_right N.add 0%N
      (map (fun ka => (64 * (M.c_map + 1) * N.of_nat (K.bits (fst ka) + 1))%N)
        (M.elements m)) <= 64 * (M.c_map + 1) * work)%N).
    { eapply N.le_trans; [exact Hlabels|].
      apply N.mul_le_mono_l. exact Hlabels_work. }
    assert (Hpotential' : (32 * N.of_nat (ell m + 1) *
      N.of_nat (length (M.codes (M.fold (tighten_row m) m M.empty))) <= 32 * work)%N).
    { eapply N.le_trans.
      - apply N.mul_le_mono_l. apply time_of_nat_le. exact Hcount.
      - replace (32 * N.of_nat (ell m + 1) * N.of_nat (supp m))%N with
          (32 * (N.of_nat (ell m + 1) * N.of_nat (supp m)))%N by ring.
        apply N.mul_le_mono_l. exact Hnumeric_work. }
    assert (Hinside : (N.of_nat (M.nodes m + 1) +
      snd (fold_left (fun bw ka =>
        (tighten_row m (fst bw) (fst ka) (snd ka),
          (snd bw + T_tighten_row m (fst bw) (fst ka) (snd ka))%N))
        (M.elements m) (M.empty, 0%N)) <=
      (64 * (M.c_map + 1) + 33) * work)%N).
    { eapply N.le_trans with
        (work + (64 * (M.c_map + 1) * work + 32 * work))%N.
      - apply N.add_le_mono; [exact Hnodes_work|].
        eapply N.le_trans; [exact Hpotential|].
        apply N.add_le_mono; [exact Hlabels'|exact Hpotential'].
      - replace ((64 * (M.c_map + 1) + 33) * work)%N with
          (work + (64 * (M.c_map + 1) * work + 32 * work))%N by ring.
        apply N.le_refl. }
    eapply N.le_trans; [exact Hclock|].
    eapply N.le_trans; [apply N.mul_le_mono_l; exact Hinside|].
    replace (M.c_map * ((64 * (M.c_map + 1) + 33) * work))%N with
      ((M.c_map * (64 * (M.c_map + 1) + 33)) * work)%N by ring.
    apply N.mul_le_mono_r. nia.
  Qed.

  Lemma T_replace_row_le : forall old fresh, (T_replace_row old fresh <= 3)%N.
  Proof.
    intros [old|] [fresh|]; time_step.
  Qed.

  (** The final merge reuses the old labels and the already charged cached rows. *)
  Lemma T_tighten_small : forall m,
    (T_tighten m <= 256 * (M.c_map + 1) * (M.c_map + 1) *
      N.of_nat (tightening_work m))%N.
  Proof.
    intro m.
    pose proof (T_tighten_fold_small m) as Hfold.
    pose proof (M.T_merge_le (M.t Z) (M.t Z) (M.t Z) replace_row
      (fun old fresh => T_replace_row old fresh) m
      (M.fold (tighten_row m) m M.empty) 3%N T_replace_row_le) as Hmerge.
    assert (Houter : forall p, In p (M.codes m) -> In p (support m)).
    { intros p Hp. apply support_spec. now left. }
    pose proof (nodes_support (M.t Z) m m Houter) as Hnodes.
    pose proof (nodes_support (M.t Z) (M.fold (tighten_row m) m M.empty)
      m (collected_tighten_support m)) as Hcache.
    set (work := N.of_nat (tightening_work m)) in *.
    assert (Hpositive : (1 <= work)%N) by (unfold work, tightening_work; lia).
    assert (Hmerge' : (M.T_merge replace_row
      (fun old fresh => T_replace_row old fresh) m
      (M.fold (tighten_row m) m M.empty) <= 8 * M.c_map * work)%N).
    { eapply N.le_trans; [exact Hmerge|].
      replace (8 * M.c_map * work)%N with ((M.c_map * (3 + 1)) * (2 * work))%N by ring.
      apply N.mul_le_mono_l. unfold work.
      assert (Hsize : M.nodes m + M.nodes (M.fold (tighten_row m) m M.empty) + 1 <=
        2 * tightening_work m) by (unfold tightening_work; nia).
      pose proof (time_of_nat_le _ _ Hsize) as Hcast.
      rewrite Nat2N.inj_mul in Hcast. exact Hcast. }
    assert (Hcoefficient : (128 * (M.c_map + 1) * (M.c_map + 1) +
      8 * M.c_map + 1 <= 256 * (M.c_map + 1) * (M.c_map + 1))%N) by nia.
    pose proof (N.mul_le_mono_r _ _ work Hcoefficient) as Htotal.
    rewrite !N.mul_add_distr_r, N.mul_1_l in Htotal.
    unfold T_tighten. time_simpl.
    match goal with
    | |- context [M.T_fold ?step ?callback m M.empty] =>
      assert (Hfold_actual : (M.T_fold step callback m M.empty <=
        128 * (M.c_map + 1) * (M.c_map + 1) * work)%N) by exact Hfold;
      set (fold_cost := M.T_fold step callback m M.empty) in *
    end.
    match goal with
    | |- context [M.T_merge ?step ?callback m ?cache] =>
      assert (Hmerge_actual : (M.T_merge step callback m cache <=
        8 * M.c_map * work)%N) by exact Hmerge';
      set (merge_cost := M.T_merge step callback m cache) in *
    end.
    clearbody work fold_cost merge_cost.
    clear - Hfold_actual Hmerge_actual Hpositive Htotal. lia.
  Qed.

  Lemma T2_tighten : forall m, dbm_wf m ->
    (T_tighten m <= k_octagon * N.of_nat ((supp m + 1)^2 * (b m + ell m + 1)))%N.
  Proof.
    intros m Hwf. pose proof (T_tighten_small m) as Hclock.
    pose proof (weight_le m Hwf) as Hweight.
    assert (Hwork : tightening_work m <=
      4 * ((supp m + 1)^2 * (b m + ell m + 1))).
    { unfold tightening_work. cbn [Nat.pow]. nia. }
    pose proof (time_of_nat_le _ _ Hwork) as Hcast.
    rewrite Nat2N.inj_mul in Hcast.
    eapply N.le_trans; [exact Hclock|].
    eapply N.le_trans; [apply N.mul_le_mono_l; exact Hcast|].
    replace (256 * (M.c_map + 1) * (M.c_map + 1) *
      (N.of_nat 4 * N.of_nat ((supp m + 1)^2 * (b m + ell m + 1))))%N with
      ((256 * (M.c_map + 1) * (M.c_map + 1) * 4) *
        N.of_nat ((supp m + 1)^2 * (b m + ell m + 1)))%N by (cbn [N.of_nat]; ring).
    apply N.mul_le_mono_r. unfold k_octagon. nia.
  Qed.


  (** Comparing zero to a diagonal has no dependence on the stored integer width. *)
  Lemma T_nonnegative_small : forall k m,
    (T_nonnegative k m <= 16 * (M.c_map + 1) * N.of_nat (K.bits k + 1))%N.
  Proof.
    intros k m. pose proof (T_entry_small m k k) as Hentry. time_step.
  Qed.

  Lemma tclose_scan_clock : forall A (f : A -> bool) tf c xs,
    Forall (fun x => (tf x <= c)%N) xs ->
    (List.T_forallb f tf xs <= (c + 2) * N.of_nat (length xs) + 1)%N.
  Proof.
    intros A f tf c xs Hbounds.
    induction Hbounds as [|x xs Hhead Htail IH]; time_step.
  Qed.

  (** Both closure scans use the original supported keys and a width-independent comparison. *)
  Lemma T_original_diagonal_scan : forall m next, dbm_wf m ->
    (List.T_forallb (fun k => nonnegative k next)
      (fun k => (1 + T_nonnegative k next)%N) (keys m) <=
      32 * (M.c_map + 1) * N.of_nat ((supp m + 1)^2 * (b m + ell m + 1)))%N.
  Proof.
    intros m next Hwf.
    set (c := (M.c_map + 1)%N).
    set (units := N.of_nat (b m + 1)).
    set (count := N.of_nat (length (keys m))).
    assert (Hunit : (1 <= units)%N) by (unfold units; lia).
    assert (Hc : (1 <= c)%N) by (unfold c; lia).
    assert (Hcallback : Forall (fun k =>
      ((1 + T_nonnegative k next)%N <= 16 * c * units + 1)%N) (keys m)).
    { apply Forall_forall. intros k Hkey.
      assert (Hbits : K.bits k <= b m).
      { unfold K.bits. apply support_bits. now apply keys_support. }
      pose proof (T_nonnegative_small k next) as Hclock.
      assert (Hcast : (N.of_nat (K.bits k + 1) <= units)%N).
      { unfold units. apply time_of_nat_le. lia. }
      assert (Hclock' : (T_nonnegative k next <= 16 * c * units)%N).
      { eapply N.le_trans; [exact Hclock|]. unfold c. now apply N.mul_le_mono_l. }
      lia. }
    pose proof (tclose_scan_clock K.t (fun k => nonnegative k next)
      (fun k => (1 + T_nonnegative k next)%N) (16 * c * units + 1)%N
      (keys m) Hcallback) as Hscan.
    fold count in Hscan.
    assert (Hlinear : ((16 * c * units + 1 + 2) * count + 1 <=
      32 * c * N.of_nat ((length (keys m) + 1) * (b m + 1)))%N).
    { assert (Hcast : N.of_nat ((length (keys m) + 1) * (b m + 1)) =
        ((count + 1) * units)%N).
      { unfold units, count. rewrite Nat2N.inj_mul.
        rewrite (Nat2N.inj_add (length (keys m)) 1). reflexivity. }
      replace (32 * c * N.of_nat ((length (keys m) + 1) * (b m + 1)))%N with
        (32 * (c * units) * (count + 1))%N
        by (rewrite Hcast; ring).
      replace (16 * c * units)%N with (16 * (c * units))%N by ring.
      assert (Hrate : (1 <= c * units)%N) by nia.
      set (rate := (c * units)%N) in *. clearbody rate. nia. }
    assert (Hwork : (length (keys m) + 1) * (b m + 1) <=
      (supp m + 1)^2 * (b m + ell m + 1)).
    { apply Nat.mul_le_mono.
      - pose proof (keys_le m Hwf). cbn [Nat.pow]. nia.
      - lia. }
    eapply N.le_trans; [exact Hscan|]. eapply N.le_trans; [exact Hlinear|].
    unfold c. apply N.mul_le_mono_l. now apply time_of_nat_le.
  Qed.

  (** The common closure coefficient includes both diagonal scans and fixed control work. *)
  Lemma k_octagon_frame_le : (64 * (M.c_map + 1) + 8 <= k_octagon)%N.
  Proof.
    unfold k_octagon. nia.
  Qed.

  (** Tight closure adds only bounded scans around its three numeric stages. *)
  Lemma T4_tclose : forall m, dbm_wf m ->
    (T_tclose m <= T_fw m + k_octagon * N.of_nat ((supp m + 1)^2 * (b m + ell m + 1)) +
      if diag_ok (fw m) then T_tighten (fw m) + T_strengthen (tighten (fw m)) else 0)%N.
  Proof.
    intros m Hwf.
    set (work := N.of_nat ((supp m + 1)^2 * (b m + ell m + 1))).
    assert (Hpositive : 1 <= (supp m + 1)^2 * (b m + ell m + 1))
      by (cbn [Nat.pow]; nia).
    pose proof (time_of_nat_le _ _ Hpositive) as Hunit.
    change (1 <= work)%N in Hunit.
    assert (Hscan : forall next,
      (List.T_forallb (fun k => nonnegative k next) (fun k => (1 + T_nonnegative k next)%N)
        (keys m) <= 32 * (M.c_map + 1) * work)%N).
    { intro next. unfold work. now apply T_original_diagonal_scan. }
    pose proof (T_tclose_overhead m (32 * (M.c_map + 1) * work)%N Hwf Hscan) as Hclock.
    pose proof (N.mul_le_mono_r _ _ work k_octagon_frame_le) as Hbudget.
    rewrite N.mul_add_distr_r in Hbudget.
    replace (64 * (M.c_map + 1) * work)%N with
      (2 * (32 * (M.c_map + 1) * work))%N in Hbudget by ring.
    clear Hpositive. clearbody work. lia.
  Qed.
  (** Consistent labels inject into any raw support containing their stored codes. *)
  Lemma elements_support_length : forall A (r : M.t A) m, M.wf r ->
    (forall p, In p (M.codes r) -> In p (support m)) ->
    length (M.elements r) <= supp m.
  Proof.
    intros A r m Hwf Hsupport.
    assert (Hlength : length (map K.encode (map fst (M.elements r))) <= supp m).
    { unfold supp. apply NoDup_incl_length.
      - apply encoded_keys_nodup. now apply M.elements_nodup.
      - intros p Hin. apply in_map_iff in Hin. destruct Hin as [k [Hcode Hkey]].
        subst p. apply Hsupport. now apply elements_code. }
    now rewrite !length_map in Hlength.
  Qed.

  (** The bit length of a consistent stored label is bounded by its raw support. *)
  Lemma elements_support_bits : forall A (r : M.t A) m k a, M.wf r ->
    (forall p, In p (M.codes r) -> In p (support m)) ->
    In (k, a) (M.elements r) -> K.bits k <= b m.
  Proof.
    intros A r m k a Hwf Hsupport Hin. unfold K.bits. apply support_bits, Hsupport.
    apply elements_code; [exact Hwf|]. apply in_map_iff. exists (k, a). now split.
  Qed.

  (** Consistent label weight is bounded by raw support size and key bits. *)
  Lemma weight_support_bound : forall A (r : M.t A) m, M.wf r ->
    (forall p, In p (M.codes r) -> In p (support m)) ->
    M.weight r <= supp m * (b m + 1).
  Proof.
    intros A r m Hwf Hsupport.
    pose proof (elements_support_length A r m Hwf Hsupport) as Hlength.
    assert (Hweight : M.weight r <= length (M.elements r) * (b m + 1)).
    { unfold M.weight. apply sum_members_bound. intros [k a] Hin. cbn [fst].
      pose proof (elements_support_bits A r m k a Hwf Hsupport Hin) as Hbits.
      unfold K.bits in Hbits. lia. }
    eapply Nat.le_trans; [exact Hweight|]. now apply Nat.mul_le_mono_r.
  Qed.

  (** Enumerating consistent labels fits the same raw support and key-bit budget. *)
  Lemma T_elements_support : forall A (r : M.t A) m, M.wf r ->
    (forall p, In p (M.codes r) -> In p (support m)) ->
    (M.T_elements r <= M.c_map * N.of_nat (supp m * (b m + 1) + 1))%N.
  Proof.
    intros A r m Hwf Hsupport.
    eapply N.le_trans; [now apply M.T_elements_le|].
    apply N.mul_le_mono_l, time_of_nat_le.
    pose proof (weight_support_bound A r m Hwf Hsupport) as Hweight. lia.
  Qed.

  (** Projecting enumerated keys adds only a linear pass to label enumeration. *)
  Lemma T_element_keys_le : forall A (r : M.t A) m, M.wf r ->
    (forall p, In p (M.codes r) -> In p (support m)) ->
    (M.T_elements r + ListDef.T_map (@fst K.t A) (fun p => Datatypes.T_fst p)
      (M.elements r) + 1 <=
      (M.c_map + 4) * N.of_nat ((supp m + 1) * (b m + 1)))%N.
  Proof.
    intros A r m Hwf Hsupport.
    pose proof (elements_support_length A r m Hwf Hsupport) as Hlength.
    pose proof (T_elements_support A r m Hwf Hsupport) as Helements.
    pose proof (@ListDef.T_map_le (K.t * A) K.t (@fst K.t A)
      (fun p => Datatypes.T_fst p) 1%N (M.elements r)
      (fun p => Datatypes.T_fst_le p)) as Hmap.
    set (work := N.of_nat ((supp m + 1) * (b m + 1))).
    assert (HlengthN : (N.of_nat (length (M.elements r)) + 1 <= work)%N).
    { replace (N.of_nat (length (M.elements r)) + 1)%N with
        (N.of_nat (length (M.elements r) + 1)) by (rewrite Nat2N.inj_add; reflexivity).
      unfold work. apply time_of_nat_le. nia. }
    assert (HdataN : (N.of_nat (supp m * (b m + 1) + 1) <= work)%N).
    { unfold work. apply time_of_nat_le. nia. }
    assert (Helements_work : (M.T_elements r <= M.c_map * work)%N).
    { eapply N.le_trans; [exact Helements|]. now apply N.mul_le_mono_l. }
    match goal with
    | |- N.le ?clock _ => change (clock <= (M.c_map + 4) * work)%N
    end.
    rewrite N.mul_add_distr_r.
    clear Hlength Helements HdataN. clearbody work. lia.
  Qed.

  (** Each enumerated matrix row is consistent and lies inside the matrix support. *)
  Lemma elements_row_support : forall m k row, dbm_wf m ->
    In (k, row) (M.elements m) -> M.wf row /\
      (forall p, In p (M.codes row) -> In p (support m)).
  Proof.
    intros m k row [Houter Hrows] Hin.
    pose proof (proj1 (M.elements_spec (M.t Z) m k row Houter) Hin) as Hget.
    rewrite M.get_find in Hget. split.
    - exact (Hrows (K.encode k) row Hget).
    - intros p Hp. apply support_spec. right. apply in_flat_map. exists row. split.
      + exact (row_in_rows m (K.encode k) row Hget).
      + exact Hp.
  Qed.

  (** Flattening lists of uniformly bounded length multiplies the two list counts. *)
  Lemma flat_map_length_bound : forall A B (f : A -> list B) xs n,
    (forall x, In x xs -> length (f x) <= n) ->
    length (flat_map f xs) <= length xs * n.
  Proof.
    intros A B f xs. induction xs as [|x xs IH]; intros n Hbound.
    - cbn. lia.
    - cbn [flat_map length]. rewrite length_app.
      assert (Hhead : length (f x) <= n) by (apply Hbound; now left).
      assert (Htail : length (flat_map f xs) <= length xs * n).
      { apply IH. intros y Hy. apply Hbound. now right. }
      lia.
  Qed.

  (** The raw pivot-label list precedes duplicate removal in the executable collector. *)
  Definition pivot_inputs (m : dbm) : list K.t :=
    map fst (M.elements m) ++
      flat_map (fun kv => map fst (M.elements (snd kv))) (M.elements m).

  (** The pivot input list has at most one outer and one inner label per supported pair. *)
  Lemma pivot_inputs_length : forall m, dbm_wf m ->
    length (pivot_inputs m) + 1 <= (supp m + 1)^2.
  Proof.
    intros m Hwf.
    assert (Houter : length (M.elements m) <= supp m).
    { apply elements_support_length; [exact (proj1 Hwf)|].
      intros p Hp. apply support_spec. now left. }
    assert (Hinner : length (flat_map (fun kv => map fst (M.elements (snd kv)))
      (M.elements m)) <= length (M.elements m) * supp m).
    { apply flat_map_length_bound. intros [k row] Hin. cbn [snd]. rewrite length_map.
      destruct (elements_row_support m k row Hwf Hin) as [Hrow Hsupport].
      now apply elements_support_length. }
    unfold pivot_inputs. rewrite length_app, length_map. cbn [Nat.pow]. nia.
  Qed.

  (** Every pivot-input label has the key-bit bound of the original matrix. *)
  Lemma pivot_inputs_bits : forall m k, dbm_wf m ->
    In k (pivot_inputs m) -> K.bits k <= b m.
  Proof.
    intros m k Hwf Hin. unfold pivot_inputs in Hin. apply in_app_iff in Hin.
    destruct Hin as [Hin|Hin].
    - apply in_map_iff in Hin. destruct Hin as [[q row] [Heq Hin]]. cbn in Heq. subst q.
      apply (elements_support_bits (M.t Z) m m k row (proj1 Hwf)); [|exact Hin].
      intros p Hp. apply support_spec. now left.
    - apply in_flat_map in Hin. destruct Hin as [[q row] [Hrow Hin]]. cbn [snd] in Hin.
      apply in_map_iff in Hin. destruct Hin as [[p z] [Heq Hin]]. cbn in Heq. subst p.
      destruct (elements_row_support m q row Hwf Hrow) as [Hrow_wf Hsupport].
      exact (elements_support_bits Z row m k z Hrow_wf Hsupport Hin).
  Qed.

  (** Mapping needs a callback bound only at members of its actual input. *)
  Lemma map_clock_members : forall A B (f : A -> B) tf c xs,
    Forall (fun x => (tf x <= c)%N) xs ->
    (ListDef.T_map f tf xs <= (c + 1) * N.of_nat (length xs) + 1)%N.
  Proof.
    intros A B f tf c xs Hbounds.
    induction Hbounds as [|x xs Hhead Htail IH]; time_step.
  Qed.

  (** An accumulator fold needs a uniform bound only for the input values it visits. *)
  Lemma fold_left_clock_members : forall A B (f : A -> B -> A) tf c xs,
    Forall (fun x => forall acc, (tf acc x <= c)%N) xs -> forall acc,
    (List.T_fold_left f tf xs acc <= (c + 1) * N.of_nat (length xs) + 1)%N.
  Proof.
    intros A B f tf c xs Hbounds.
    induction Hbounds as [|x xs Hhead Htail IH]; intro acc; time_step.
  Qed.

  (** A Boolean scan needs callback bounds only at members of its input list. *)
  Lemma forallb_clock_members : forall A (f : A -> bool) tf c xs,
    Forall (fun x => (tf x <= c)%N) xs ->
    (List.T_forallb f tf xs <= (c + 2) * N.of_nat (length xs) + 1)%N.
  Proof.
    intros A f tf c xs Hbounds.
    induction Hbounds as [|x xs Hhead Htail IH]; time_step.
  Qed.

  (** Flattening pays a callback and one concatenation per outer input value. *)
  Lemma flat_map_clock_members : forall A B (f : A -> list B) tf c n xs,
    Forall (fun x => (tf x <= c)%N /\ length (f x) <= n) xs ->
    (List.T_flat_map f tf xs <=
      (c + N.of_nat n + 2) * N.of_nat (length xs) + 1)%N.
  Proof.
    intros A B f tf c n xs Hbounds.
    induction Hbounds as [|x xs [Hhead Hlength] Htail IH].
    - time_step.
    - pose proof (time_of_nat_le _ _ Hlength) as HlengthN. time_step.
  Qed.

  (** Remembering a key charges its encoded key length independently of accumulated keys. *)
  Lemma T_remember_key_le : forall acc k,
    (T_remember_key acc k <= 8 * (M.c_map + 1) * N.of_nat (K.bits k + 1))%N.
  Proof.
    intros [seen ks] k. time_step.
  Qed.

  (** The map-backed deduplication fold pays each input's key bits once. *)
  Lemma T_remember_fold_le : forall ks acc bb,
    (forall k, In k ks -> K.bits k <= bb) ->
    (List.T_fold_left remember_key (fun a k => T_remember_key a k) ks acc <=
      16 * (M.c_map + 1) * N.of_nat ((length ks + 1) * (bb + 1)))%N.
  Proof.
    intros ks acc bb Hbits.
    assert (Hcallback : Forall (fun k => forall a,
      (T_remember_key a k <= 8 * (M.c_map + 1) * N.of_nat (bb + 1))%N) ks).
    { apply Forall_forall. intros k Hin a.
      eapply N.le_trans; [apply T_remember_key_le|].
      apply N.mul_le_mono_l, time_of_nat_le. pose proof (Hbits k Hin). lia. }
    pose proof (fold_left_clock_members (M.t unit * list K.t) K.t remember_key
      (fun a k => T_remember_key a k) (8 * (M.c_map + 1) * N.of_nat (bb + 1))%N
      ks Hcallback acc) as Hfold.
    clear Hbits Hcallback.
    rewrite (Nat2N.inj_mul (length ks + 1) (bb + 1)), Nat2N.inj_add.
    set (count := N.of_nat (length ks)) in *.
    set (bits := N.of_nat (bb + 1)) in *.
    assert (Hbits : (1 <= bits)%N) by (unfold bits; lia).
    clearbody count bits.
    set (work := ((count + 1) * bits)%N).
    assert (Hunit : (1 <= work)%N) by (unfold work; nia).
    assert (Hper : (8 * (M.c_map + 1) * bits + 1 <=
      9 * (M.c_map + 1) * bits)%N) by nia.
    assert (Hfold_work : (List.T_fold_left remember_key
      (fun a k => T_remember_key a k) ks acc <= 9 * (M.c_map + 1) * work + 1)%N).
    { eapply N.le_trans; [exact Hfold|]. apply N.add_le_mono_r.
      eapply N.le_trans; [apply N.mul_le_mono_r; exact Hper|].
      replace (9 * (M.c_map + 1) * work)%N with
        (9 * (M.c_map + 1) * bits * (count + 1))%N by (unfold work; ring).
      apply N.mul_le_mono_l. lia. }
    match goal with
    | |- N.le ?clock _ => change (clock <= 16 * (M.c_map + 1) * work)%N
    end.
    assert (Hbudget : ((9 * (M.c_map + 1) + 1) * work <=
      16 * (M.c_map + 1) * work)%N).
    { apply N.mul_le_mono_r. lia. }
    rewrite N.mul_add_distr_r, N.mul_1_l in Hbudget.
    clear Hfold Hper Hbits. clearbody work. lia.
  Qed.

  (** The trace cost records precisely the rounds performed by the executable loop. *)
  Definition trace_cost (ks : list K.t) (m : dbm) : N :=
    fold_right N.add 0%N (map (fun km => T_fw_round (fst km) (snd km)) (fw_trace ks m)).

  (** One trace entry pays its round and continues exactly when the diagonal is nonnegative. *)
  Lemma trace_cost_cons : forall k ks m,
    trace_cost (k :: ks) m = (T_fw_round k m +
      if nonnegative k (fw_round k m) then trace_cost ks (fw_round k m) else 0)%N.
  Proof.
    intros k ks m. unfold trace_cost at 1. rewrite fw_trace_nonnegative.
    cbn [map fold_right fst snd]. destruct (nonnegative k (fw_round k m)); reflexivity.
  Qed.

  (** Each key has a diagonal-check budget independent of the current matrix entries. *)
  Definition diagonal_budget (k : K.t) : N :=
    (16 * (M.c_map + 1) * N.of_nat (K.bits k + 1) + 4)%N.

  Definition scan_budget (ks : list K.t) : N := fold_right N.add 0%N (map diagonal_budget ks).

  (** The pivot loop pays its traced rounds, one diagonal check per key, and loop overhead. *)
  Lemma T_fw_pivots_trace : forall ks m,
    (T_fw_pivots ks m <= trace_cost ks m + scan_budget ks + 1)%N.
  Proof.
    intro ks. induction ks as [|k ks IH]; intro m.
    - unfold trace_cost, scan_budget. cbn [fw_trace map fold_right]. time_step.
    - rewrite trace_cost_cons.
      change (T_fw_pivots (k :: ks) m <=
        T_fw_round k m +
          (if nonnegative k (fw_round k m) then trace_cost ks (fw_round k m) else 0) +
        (diagonal_budget k + scan_budget ks) + 1)%N.
      pose proof (T_nonnegative_small k (fw_round k m)) as Hdiag.
      specialize (IH (fw_round k m)).
      time_unfold (@T_fw_pivots). cbn beta iota zeta.
      destruct (nonnegative k (fw_round k m)); cbn beta iota zeta;
        unfold diagonal_budget; lia.
  Qed.

  (** The final diagonal scan fits the same per-key budget as the pivot loop. *)
  Lemma T_diagonal_scan_le : forall ks m,
    (List.T_forallb (fun k => nonnegative k m) (fun k => (1 + T_nonnegative k m)%N) ks <=
      scan_budget ks + 1)%N.
  Proof.
    intro ks. induction ks as [|k ks IH]; intro m.
    - unfold scan_budget. cbn [map fold_right]. time_step.
    - change (List.T_forallb (fun k => nonnegative k m) (fun k => (1 + T_nonnegative k m)%N)
        (k :: ks) <= diagonal_budget k + scan_budget ks + 1)%N.
      pose proof (T_nonnegative_small k m) as Hdiag. specialize (IH m).
      unfold diagonal_budget. time_step.
  Qed.

  (** Uniform key bits bound the sum of diagonal budgets. *)
  Lemma scan_budget_bound : forall ks bb,
    (forall k, In k ks -> K.bits k <= bb) ->
    (scan_budget ks <= 20 * (M.c_map + 1) * N.of_nat (length ks * (bb + 1)))%N.
  Proof.
    intros ks bb Hbits.
    assert (Hpoint : forall k, In k ks ->
      (diagonal_budget k <= 20 * (M.c_map + 1) * N.of_nat (bb + 1))%N).
    { intros k Hin. pose proof (Hbits k Hin) as Hkey.
      assert (HkeyN : (N.of_nat (K.bits k + 1) <= N.of_nat (bb + 1))%N)
        by (apply time_of_nat_le; lia).
      assert (Hunit : (1 <= N.of_nat (bb + 1))%N) by lia.
      pose proof (N.mul_le_mono_l _ _ (16 * (M.c_map + 1))%N HkeyN) as Hscaled.
      unfold diagonal_budget. nia. }
    pose proof (time_sum_bound K.t ks diagonal_budget (fun _ => bb + 1)
      (20 * (M.c_map + 1))%N Hpoint) as Hsum.
    now rewrite sum_weight_const in Hsum.
  Qed.

  (** The deduplicated pivot scan fits the matrix's initial quadratic work. *)
  Lemma scan_budget_keys : forall m, dbm_wf m ->
    (scan_budget (keys m) <= 20 * (M.c_map + 1) *
      N.of_nat ((supp m + 1)^2 * (b m + ell m + 1)))%N.
  Proof.
    intros m Hwf. eapply N.le_trans; [apply (scan_budget_bound (keys m) (b m))|].
    - intros k Hin. unfold K.bits. apply support_bits. now apply keys_support.
    - apply N.mul_le_mono_l, time_of_nat_le.
      pose proof (keys_le m Hwf) as Hlength. cbn [Nat.pow]. nia.
  Qed.
  (** Collecting and deduplicating pivot labels fits the initial quadratic key budget. *)
  Lemma T_pivot_keys_le : forall m, dbm_wf m ->
    (T_pivot_keys m <= 64 * (M.c_map + 1) *
      N.of_nat ((supp m + 1)^2 * (b m + 1)))%N.
  Proof.
    intros m Hwf.
    assert (Hsupport : forall p, In p (M.codes m) -> In p (support m)).
    { intros p Hp. apply support_spec. now left. }
    pose proof (elements_support_length (M.t Z) m m (proj1 Hwf) Hsupport) as Hlength.
    pose proof (pivot_inputs_length m Hwf) as Hinputs.
    set (rowwork := N.of_nat ((supp m + 1) * (b m + 1))).
    set (work := N.of_nat ((supp m + 1)^2 * (b m + 1))).
    assert (Hpositive : 1 <= (supp m + 1)^2 * (b m + 1))
      by (cbn [Nat.pow]; nia).
    pose proof (time_of_nat_le _ _ Hpositive) as Hunit.
    change (1 <= work)%N in Hunit.
    assert (Hrowunit : (N.of_nat (supp m) + 1 <= rowwork)%N).
    { replace (N.of_nat (supp m) + 1)%N with (N.of_nat (supp m + 1))
        by (rewrite Nat2N.inj_add; reflexivity).
      unfold rowwork. apply time_of_nat_le. nia. }
    assert (Hrowwork : (rowwork <= work)%N).
    { unfold rowwork, work. apply time_of_nat_le. cbn [Nat.pow]. nia. }
    assert (Hrowprod : (rowwork * N.of_nat (length (M.elements m)) <= work)%N).
    { unfold rowwork, work. rewrite <- Nat2N.inj_mul.
      apply time_of_nat_le. cbn [Nat.pow]. nia. }
    pose proof (T_element_keys_le (M.t Z) m m (proj1 Hwf) Hsupport) as Houter.
    assert (Houter_work : (M.T_elements m + ListDef.T_map (@fst K.t (M.t Z))
      (fun p => Datatypes.T_fst p) (M.elements m) + 1 <= (M.c_map + 4) * work)%N).
    { eapply N.le_trans; [exact Houter|]. now apply N.mul_le_mono_l. }
    pose proof (T_remember_fold_le (pivot_inputs m) (M.empty, nil) (b m)
      (fun k Hin => pivot_inputs_bits m k Hwf Hin)) as Hremember.
    assert (Hremember_work : (List.T_fold_left remember_key
      (fun a k => T_remember_key a k) (pivot_inputs m) (M.empty, nil) <=
      16 * (M.c_map + 1) * work)%N).
    { eapply N.le_trans; [exact Hremember|]. apply N.mul_le_mono_l.
      unfold work. apply time_of_nat_le. now apply Nat.mul_le_mono_r. }
    assert (Happ_work : (Datatypes.T_app (map fst (M.elements m))
      (flat_map (fun kv => map fst (M.elements (snd kv))) (M.elements m)) <= work)%N).
    { eapply N.le_trans; [apply Datatypes.T_app_le|]. rewrite length_map.
      replace (N.of_nat (length (M.elements m)) + 1)%N with
        (N.of_nat (length (M.elements m) + 1)) by (rewrite Nat2N.inj_add; reflexivity).
      unfold work. apply time_of_nat_le. cbn [Nat.pow]. nia. }
    unfold T_pivot_keys. cbn beta iota zeta.
    match goal with
    | |- context [List.T_flat_map ?f ?tf (M.elements m)] =>
      assert (Hrows : Forall (fun kv =>
        (tf kv <= (M.c_map + 5) * rowwork)%N /\ length (f kv) <= supp m)
        (M.elements m));
      [ apply Forall_forall; intros [k row] Hin;
        destruct (elements_row_support m k row Hwf Hin) as [Hrow Hrow_support]; split;
        [ pose proof (T_element_keys_le Z row m Hrow Hrow_support) as Hrow_clock;
          fold rowwork in Hrow_clock;
          cbv beta delta [Datatypes.T_fst] in Hrow_clock;
          cbn beta iota zeta; time_simpl; cbn [fst snd];
          replace ((M.c_map + 5) * rowwork)%N with
            ((M.c_map + 4) * rowwork + rowwork)%N by ring; lia
        | cbn [snd]; rewrite length_map; now apply elements_support_length ]
      | pose proof (flat_map_clock_members (K.t * M.t Z) K.t f tf
          ((M.c_map + 5) * rowwork)%N (supp m) (M.elements m) Hrows) as Hflat;
        assert (Hper : ((M.c_map + 5) * rowwork + N.of_nat (supp m) + 2 <=
          (M.c_map + 7) * rowwork)%N);
        [ replace ((M.c_map + 7) * rowwork)%N with
            ((M.c_map + 5) * rowwork + 2 * rowwork)%N by ring; lia
        | assert (Hflat_work : (List.T_flat_map f tf (M.elements m) <=
            (M.c_map + 8) * work)%N);
          [ eapply N.le_trans; [exact Hflat|];
            eapply N.le_trans with
              ((M.c_map + 7) * rowwork * N.of_nat (length (M.elements m)) + 1)%N;
            [ apply N.add_le_mono_r, N.mul_le_mono_r; exact Hper
            | replace ((M.c_map + 7) * rowwork * N.of_nat (length (M.elements m)) + 1)%N
                with ((M.c_map + 7) * (rowwork * N.of_nat (length (M.elements m))) + 1)%N
                by ring;
              eapply N.le_trans with ((M.c_map + 7) * work + 1)%N;
              [ apply N.add_le_mono_r, N.mul_le_mono_l; exact Hrowprod
              | replace ((M.c_map + 8) * work)%N with
                  ((M.c_map + 7) * work + work)%N by ring; lia ] ]
          | clear Hrows Hflat Hper ] ] ]
    end.
    assert (Hbudget : ((M.c_map + 4 + (M.c_map + 8) + 1 +
      16 * (M.c_map + 1) + 4) * work <= 64 * (M.c_map + 1) * work)%N).
    { apply N.mul_le_mono_r. lia. }
    repeat rewrite N.mul_add_distr_r in Hbudget.
    rewrite N.mul_add_distr_r in Houter_work, Hflat_work.
    cbv beta delta [Datatypes.T_fst Datatypes.T_snd] in Houter_work, Hflat_work.
    time_simpl. fold (pivot_inputs m).
    match goal with
    | |- N.le ?clock _ => change (clock <= 64 * (M.c_map + 1) * work)%N
    end.
    clear Houter Hremember Hlength Hinputs Hpositive Hrowunit Hrowwork Hrowprod.
    clearbody rowwork work. lia.
  Qed.

  (** Floyd-Warshall adds only collection and diagonal checks to its exact round trace. *)
  Lemma T_fw_additive : forall m, dbm_wf m ->
    (T_fw m <= trace_cost (keys m) m + 128 * (M.c_map + 1) *
      N.of_nat ((supp m + 1)^2 * (b m + ell m + 1)))%N.
  Proof.
    intros m Hwf.
    set (work := N.of_nat ((supp m + 1)^2 * (b m + ell m + 1))).
    replace (128 * (M.c_map + 1) * work)%N with
      (128 * ((M.c_map + 1) * work))%N by ring.
    assert (Hpositive : 1 <= (supp m + 1)^2 * (b m + ell m + 1))
      by (cbn [Nat.pow]; nia).
    pose proof (time_of_nat_le _ _ Hpositive) as Hunit.
    change (1 <= work)%N in Hunit.
    assert (Hcollect : (T_pivot_keys m <= 64 * ((M.c_map + 1) * work))%N).
    { eapply N.le_trans; [now apply T_pivot_keys_le|].
      replace (64 * ((M.c_map + 1) * work))%N with
        (64 * (M.c_map + 1) * work)%N by ring.
      apply N.mul_le_mono_l. unfold work. apply time_of_nat_le, Nat.mul_le_mono_l. lia. }
    pose proof (scan_budget_keys m Hwf) as Hscan.
    change (scan_budget (keys m) <= 20 * (M.c_map + 1) * work)%N in Hscan.
    replace (20 * (M.c_map + 1) * work)%N with (20 * ((M.c_map + 1) * work))%N
      in Hscan by ring.
    pose proof (T_fw_pivots_trace (keys m) m) as Hloop.
    assert (Hkeyunit : (1 <= (M.c_map + 1) * work)%N).
    { change (1 * 1 <= (M.c_map + 1) * work)%N. apply N.mul_le_mono; lia. }
    set (rounds := trace_cost (keys m) m) in *.
    set (keywork := ((M.c_map + 1) * work)%N) in *.
    clear Hpositive Hunit. clearbody work keywork rounds.
    unfold T_fw. cbn beta iota zeta. rewrite pivot_keys_eq_keys. time_simpl. lia.
  Qed.

  (** The plan coefficient covers the additive collection and scan coefficient. *)
  Lemma k_octagon_trace_coefficient : (128 * (M.c_map + 1) <= k_octagon)%N.
  Proof.
    unfold k_octagon. nia.
  Qed.

  (** Floyd-Warshall pays for pivot collection and the rounds recorded in its trace. *)
  Lemma T0_fw : forall m, dbm_wf m ->
    (T_fw m <= k_octagon * (N.of_nat ((supp m + 1)^2 * (b m + ell m + 1)) +
      fold_right N.add 0%N (map (fun km => T_fw_round (fst km) (snd km))
        (fw_trace (keys m) m))))%N.
  Proof.
    intros m Hwf. pose proof (T_fw_additive m Hwf) as Htime.
    set (work := N.of_nat ((supp m + 1)^2 * (b m + ell m + 1))) in *.
    change (T_fw m <= k_octagon * (work + trace_cost (keys m) m))%N.
    set (rounds := trace_cost (keys m) m) in *.
    pose proof k_octagon_trace_coefficient as Hcoefficient.
    assert (Hconstant : (1 <= k_octagon)%N) by lia.
    assert (Hframe : (128 * (M.c_map + 1) * work <= k_octagon * work)%N)
      by (now apply N.mul_le_mono_r).
    assert (Hrounds : (rounds <= k_octagon * rounds)%N).
    { replace rounds with (1 * rounds)%N at 1 by ring. now apply N.mul_le_mono_r. }
    rewrite N.mul_add_distr_l. lia.
  Qed.
  (** A label-bounded fold charges the exact raw label sum, without a wf premise. *)
  Lemma T_fold_label_weight : forall (A B : Type) (step : B -> K.t -> A -> B)
      (clock : B -> K.t -> A -> N) m seed c,
    (forall acc k a, (clock acc k a <= c * N.of_nat (K.bits k + 1))%N) ->
    (M.T_fold step clock m seed <= M.c_map *
      (N.of_nat (M.nodes m + 1) + c * N.of_nat (M.weight m)))%N.
  Proof.
    intros A B step clock m seed c Hbound.
    pose proof (M.T_fold_sum_le A B step clock m seed) as Hclock.
    pose proof (fold_potential_time (K.t * A)%type B
      (fun acc ka => step acc (fst ka) (snd ka))
      (fun acc ka => clock acc (fst ka) (snd ka))
      (fun _ => 0%N) (fun ka => (c * N.of_nat (K.bits (fst ka) + 1))%N)
      (M.elements m) seed 0%N
      ltac:(intros acc [k a]; cbn [fst snd]; rewrite !N.add_0_r; apply Hbound)) as Hsum.
    cbn beta zeta in Hsum. rewrite ?N.add_0_r, ?N.add_0_l in Hsum.
    assert (Hlabels : (fold_right N.add 0%N
      (map (fun ka => (c * N.of_nat (K.bits (fst ka) + 1))%N) (M.elements m)) <=
      c * N.of_nat (M.weight m))%N).
    { change (fold_right N.add 0%N
        (map (fun ka => (c * N.of_nat (K.bits (fst ka) + 1))%N) (M.elements m)) <=
        c * N.of_nat (sum_weight (fun ka => (K.bits (fst ka) + 1)%nat) (M.elements m)))%N.
      apply time_sum_bound. intros ka Hka. apply N.le_refl. }
    eapply N.le_trans; [exact Hclock|]. apply N.mul_le_mono_l.
    apply N.add_le_mono_l. eapply N.le_trans; [exact Hsum|exact Hlabels].
  Qed.

  (** The diagonal check pays for raw labels even when several labels name the same code. *)
  Lemma T_matrix_ok_small : forall m,
    (T_matrix_ok m <= 128 * (M.c_map + 1) * (M.c_map + 1) *
      N.of_nat (M.weight m + supp m * (b m + 1) + 1))%N.
  Proof.
    intro m. unfold T_matrix_ok. time_simpl.
    match goal with
    | |- context [M.T_fold ?f ?tf m true] =>
      assert (Hcallback : forall acc k row,
        (tf acc k row <= 64 * (M.c_map + 1) * N.of_nat (K.bits k + 1))%N)
        by (intros acc k row; pose proof (T_nonnegative_small k m);
          pose proof (Std.Datatypes.T_andb_le acc (nonnegative k m));
          time_simpl; rewrite ?Nat2N.inj_add in *; nia);
      pose proof (T_fold_label_weight (M.t Z) bool f tf m true
        (64 * (M.c_map + 1))%N Hcallback) as Hfold;
      set (fold_clock := M.T_fold f tf m true) in *
    end.
    assert (Houter : forall p, In p (M.codes m) -> In p (support m)).
    { intros p Hp. apply support_spec. now left. }
    pose proof (nodes_support (M.t Z) m m Houter) as Hnodes.
    set (work := N.of_nat (M.weight m + supp m * (b m + 1) + 1)).
    assert (Hpositive : (1 <= work)%N) by (unfold work; lia).
    assert (Hnode_work : (N.of_nat (M.nodes m + 1) <= work)%N) by (unfold work; lia).
    assert (Hlabel_work : (N.of_nat (M.weight m) <= work)%N) by (unfold work; lia).
    assert (Hfold' : (fold_clock <=
      M.c_map * (64 * (M.c_map + 1) + 1) * work)%N).
    { eapply N.le_trans; [exact Hfold|].
      replace (M.c_map * (64 * (M.c_map + 1) + 1) * work)%N with
        (M.c_map * ((64 * (M.c_map + 1) + 1) * work))%N by ring.
      apply N.mul_le_mono_l.
      pose proof (N.mul_le_mono_l _ _ (64 * (M.c_map + 1))%N Hlabel_work).
      rewrite N.mul_add_distr_r, N.mul_1_l. lia. }
    assert (Hcoefficient : (M.c_map * (64 * (M.c_map + 1) + 1) + 1 <=
      128 * (M.c_map + 1) * (M.c_map + 1))%N) by nia.
    pose proof (N.mul_le_mono_r _ _ work Hcoefficient) as Hbudget.
    rewrite N.mul_add_distr_r, N.mul_1_l in Hbudget.
    clearbody work fold_clock. clear - Hfold' Hpositive Hbudget. lia.
  Qed.


  (** Payload bounds lift monotonically to the sparse map work measure. *)
  Lemma code_work_mono : forall (A : Type) (f g : A -> nat) (m : M.t A),
    (forall p a, M.find p m = Some a -> f a <= g a) ->
    code_work f m <= code_work g m.
  Proof.
    intros A f g m Hbound. unfold code_work, stored_weight.
    assert (Hsum : sum_weight (fun p => option_weight f (M.find p m)) (M.codes m) <=
      sum_weight (fun p => option_weight g (M.find p m)) (M.codes m)).
    { apply sum_weight_mono. intros p Hp.
      destruct (M.find p m) as [a|] eqn:Ha; cbn [option_weight].
      - now apply (Hbound p a).
      - lia. }
    lia.
  Qed.

  (** Both unary maps contain only codes already supported by the source matrix. *)
  Lemma collect_unary_support : forall m,
    (forall p, In p (M.codes (fst (M.fold (unary_maps m) m (M.empty, M.empty)))) ->
      In p (support m)) /\
    (forall p, In p (M.codes (snd (M.fold (unary_maps m) m (M.empty, M.empty)))) ->
      In p (support m)).
  Proof.
    intro m. destruct (collect_unary_origins m) as [Hleft Hright]. split.
    - intros p Hp. apply M.codes_spec in Hp.
      destruct (M.find p (fst (M.fold (unary_maps m) m (M.empty, M.empty))))
        as [d|] eqn:Hfind; [|contradiction].
      destruct (Hleft p d Hfind) as [k [Hkey Hsource]]. subst p.
      apply support_find. left. unfold entry in Hsource. rewrite M.get_find in Hsource.
      destruct (M.find (K.encode k) m); congruence.
    - intros p Hp. apply M.codes_spec in Hp.
      destruct (M.find p (snd (M.fold (unary_maps m) m (M.empty, M.empty))))
        as [d|] eqn:Hfind; [|contradiction].
      destruct (Hright p d Hfind) as [k [Hkey Hsource]]. subst p.
      apply support_find. right. exists (K.encode k).
      rewrite raw_entry_get, Hsource. discriminate.
  Qed.

  Lemma collect_unary_bits : forall m,
    (forall p d, M.find p (fst (M.fold (unary_maps m) m (M.empty, M.empty))) = Some d ->
      Z.size_nat d <= ell m) /\
    (forall p d, M.find p (snd (M.fold (unary_maps m) m (M.empty, M.empty))) = Some d ->
      Z.size_nat d <= ell m).
  Proof.
    intro m. destruct (collect_unary_origins m) as [Hleft Hright]. split.
    - intros p d Hd. destruct (Hleft p d Hd) as [k [Hkey Hsource]].
      eapply ell_entry. rewrite raw_entry_get. exact Hsource.
    - intros p d Hd. destruct (Hright p d Hd) as [k [Hkey Hsource]].
      eapply ell_entry. rewrite raw_entry_get. exact Hsource.
  Qed.

  (** Collecting a unary payload performs only key operations, independently of its bit length. *)
  Lemma T_unary_maps_le : forall m acc k ignored,
    (T_unary_maps m acc k ignored <=
      64 * (M.c_map + 1) * N.of_nat (K.bits k + 1))%N.
  Proof.
    intros m acc k ignored. pose proof (flip_bits k) as Hbits.
    pose proof (T_flip_le k) as Hflip.
    pose proof (T_entry_small m k (flip k)) as Hentry.
    pose proof (Std.Datatypes.T_fst_le acc) as Hfst.
    pose proof (Std.Datatypes.T_snd_le acc) as Hsnd.
    unfold T_unary_maps. time_simpl.
    destruct (entry m k (flip k)) as [d|].
    - pose proof (M.T_set_le Z k d (fst acc)) as Hleft.
      pose proof (M.T_set_le Z (flip k) d (snd acc)) as Hright.
      time_simpl. rewrite ?Nat2N.inj_add in *. first [time_lin|nia].
    - time_simpl. rewrite ?Nat2N.inj_add in *. first [time_lin|nia].
  Qed.

  (** The average callback charges its prefix only at finite unary suffixes. *)
  Lemma T_strengthen_bound_le : forall a old unary,
    (T_strengthen_bound a old unary <= 32 * N.of_nat
      (option_weight (fun b => (Z.size_nat a + Z.size_nat b + 1)%nat) unary + 1))%N.
  Proof.
    intros a old [b|]; cbn [option_weight].
    - pose proof (zbits_add_sum a b). pose proof (zbits_div2 (a + b)%Z). time_step.
    - time_step.
  Qed.

  Local Definition strengthening_row_work (unaries : M.t Z) (a : Z) : nat :=
    code_work (fun b => (Z.size_nat a + Z.size_nat b + 1)%nat) unaries.

  Lemma T_strengthen_outer_le : forall unaries old unary,
    (T_strengthen_outer unaries old unary <= 128 * (M.c_map + 1) * N.of_nat
      (option_weight (code_work (fun _ : Z => 0%nat)) old +
        option_weight (strengthening_row_work unaries) unary + 1))%N.
  Proof.
    intros unaries [row|] [a|]; cbn [option_weight].
    - assert (Hcallback : forall old next,
        (T_strengthen_bound a old next <= 32 * N.of_nat
          (option_weight (fun _ : Z => 0%nat) old +
            option_weight (fun b => (Z.size_nat a + Z.size_nat b + 1)%nat) next + 1))%N).
      { intros old next. rewrite option_weight_zero. apply T_strengthen_bound_le. }
      pose proof (T_merge_code_work Z Z Z (strengthen_bound a)
        (fun old next => T_strengthen_bound a old next) (fun _ : Z => 0)
        (fun b => (Z.size_nat a + Z.size_nat b + 1)%nat) row unaries 32%N Hcallback) as Hmerge.
      unfold strengthening_row_work.
      set (work := N.of_nat (code_work (fun _ : Z => 0) row +
        code_work (fun b => (Z.size_nat a + Z.size_nat b + 1)%nat) unaries + 1)) in *.
      assert (Hpositive : (1 <= work)%N) by (unfold work; lia).
      assert (Hcoefficient : (M.c_map * (32 + 1) * 2 + 2 <=
        128 * (M.c_map + 1))%N) by lia.
      pose proof (N.mul_le_mono_r _ _ work Hcoefficient) as Hbudget.
      rewrite N.mul_add_distr_r in Hbudget.
      unfold T_strengthen_outer. time_simpl. clearbody work.
      clear - Hmerge Hpositive Hbudget. lia.
    - unfold T_strengthen_outer. time_simpl. nia.
    - unfold T_strengthen_outer. time_simpl. nia.
    - unfold T_strengthen_outer. time_simpl. nia.
  Qed.


  Local Definition strengthening_work (m : dbm) : nat :=
    M.weight m + (supp m + 1)^2 * (b m + ell m + 1) + 1.

  Lemma strengthening_scalar_bound : forall n bb ee,
    n * (bb + 1) + n + n * (n * (bb + 2 * ee + 3)) <=
      4 * (n + 1)^2 * (bb + ee + 1).
  Proof.
    intros n bb ee. cbn [Nat.pow]. nia.
  Qed.

  (** The outer merge charges source rows and a quadratic number of unary averages. *)
  Lemma strengthening_maps_work_bound : forall m,
    code_work (code_work (fun _ : Z => 0)) m +
      code_work
        (strengthening_row_work (snd (M.fold (unary_maps m) m (M.empty, M.empty))))
        (fst (M.fold (unary_maps m) m (M.empty, M.empty))) + 1 <=
      8 * ((supp m + 1)^2 * (b m + ell m + 1)).
  Proof.
    intro m.
    set (base := (supp m + 1)^2 * (b m + ell m + 1)).
    assert (Hpositive : 1 <= base) by (unfold base; cbn [Nat.pow]; nia).
    assert (Hsource : code_work (code_work (fun _ : Z => 0)) m <= 2 * base).
    { pose proof (matrix_code_work_le m) as Hmatrix.
      change (code_work (code_work Z.size_nat) m <= base + skel m) in Hmatrix.
      assert (Hzero : code_work (code_work (fun _ : Z => 0)) m <=
        code_work (code_work Z.size_nat) m).
      { apply code_work_mono. intros p row Hrow. apply code_work_mono.
        intros q z Hz. lia. }
      assert (Hskel : skel m <= base).
      { eapply Nat.le_trans; [apply skel_le|].
        unfold base. apply Nat.mul_le_mono_l. lia. }
      lia. }
    destruct (collect_unary_support m) as [HsupportL HsupportR].
    destruct (collect_unary_bits m) as [HbitsL HbitsR].
    set (unaries := M.fold (unary_maps m) m (M.empty, M.empty)) in *.
    pose proof (codes_support_length Z (fst unaries) m HsupportL) as Hcount.
    pose proof (nodes_support Z (fst unaries) m HsupportL) as Hnodes.
    assert (Hrowwork : forall p a, M.find p (fst unaries) = Some a ->
      strengthening_row_work (snd unaries) a <=
        supp m * (b m + 2 * ell m + 3)).
    { intros p a Ha. unfold strengthening_row_work.
      eapply Nat.le_trans.
      - apply code_work_bits_bound; [exact HsupportR|exact HbitsR].
      - apply Nat.mul_le_mono_l. pose proof (HbitsL p a Ha). lia. }
    pose proof (stored_weight_uniform Z (strengthening_row_work (snd unaries))
      (fst unaries) (supp m * (b m + 2 * ell m + 3)) Hrowwork) as Hstored.
    assert (Hstored' : stored_weight (strengthening_row_work (snd unaries)) (fst unaries) <=
      supp m * (supp m * (b m + 2 * ell m + 3))).
    { eapply Nat.le_trans; [exact Hstored|].
      apply Nat.mul_le_mono_r. exact Hcount. }
    assert (Hunaries : code_work (strengthening_row_work (snd unaries)) (fst unaries) <=
      4 * base).
    { pose proof (strengthening_scalar_bound (supp m) (b m) (ell m)) as Hscalar.
      replace (4 * (supp m + 1)^2 * (b m + ell m + 1)) with
        (4 * base) in Hscalar by (unfold base; ring).
      unfold code_work. lia. }
    lia.
  Qed.

  (** Collection charges raw labels, while the merge charges only distinct supported codes. *)
  Lemma T_strengthen_small : forall m,
    (T_strengthen m <= 4096 * (M.c_map + 1) * (M.c_map + 1) *
      N.of_nat (strengthening_work m))%N.
  Proof.
    intro m.
    pose proof (T_fold_label_weight (M.t Z) (M.t Z * M.t Z)%type (unary_maps m)
      (fun acc k row => T_unary_maps m acc k row) m (M.empty, M.empty)
      (64 * (M.c_map + 1))%N (T_unary_maps_le m)) as Hfold.
    set (unaries := M.fold (unary_maps m) m (M.empty, M.empty)).
    pose proof (T_merge_code_work (M.t Z) Z (M.t Z)
      (strengthen_outer (snd unaries))
      (fun old unary => T_strengthen_outer (snd unaries) old unary)
      (code_work (fun _ : Z => 0)) (strengthening_row_work (snd unaries))
      m (fst unaries) (128 * (M.c_map + 1))%N
      (T_strengthen_outer_le (snd unaries))) as Hmerge.
    pose proof (strengthening_maps_work_bound m) as Hmaps. fold unaries in Hmaps.
    pose proof (time_of_nat_le _ _ Hmaps) as HmapsN. rewrite Nat2N.inj_mul in HmapsN.
    assert (Houter : forall p, In p (M.codes m) -> In p (support m)).
    { intros p Hp. apply support_spec. now left. }
    pose proof (nodes_support (M.t Z) m m Houter) as Hnodes.
    set (work := N.of_nat (strengthening_work m)) in *.
    assert (Hpositive : (1 <= work)%N) by (unfold work, strengthening_work; lia).
    assert (Hbase_work :
      (N.of_nat ((supp m + 1)^2 * (b m + ell m + 1)) <= work)%N).
    { unfold work, strengthening_work. lia. }
    assert (Hnode_work : (N.of_nat (M.nodes m + 1) <= work)%N).
    { unfold work. apply time_of_nat_le. unfold strengthening_work. cbn [Nat.pow]. nia. }
    assert (Hlabel_work : (N.of_nat (M.weight m) <= work)%N).
    { unfold work, strengthening_work. lia. }
    assert (Hfold' : (M.T_fold (unary_maps m)
      (fun acc k row => T_unary_maps m acc k row) m (M.empty, M.empty) <=
      M.c_map * (64 * (M.c_map + 1) + 1) * work)%N).
    { eapply N.le_trans; [exact Hfold|].
      replace (M.c_map * (64 * (M.c_map + 1) + 1) * work)%N with
        (M.c_map * ((64 * (M.c_map + 1) + 1) * work))%N by ring.
      apply N.mul_le_mono_l.
      pose proof (N.mul_le_mono_l _ _ (64 * (M.c_map + 1))%N Hlabel_work).
      rewrite N.mul_add_distr_r, N.mul_1_l. lia. }
    assert (Hmerge' : (M.T_merge (strengthen_outer (snd unaries))
      (fun old unary => T_strengthen_outer (snd unaries) old unary) m (fst unaries) <=
      16 * M.c_map * (128 * (M.c_map + 1) + 1) * work)%N).
    { eapply N.le_trans; [exact Hmerge|].
      replace (16 * M.c_map * (128 * (M.c_map + 1) + 1) * work)%N with
        (M.c_map * (128 * (M.c_map + 1) + 1) * 2 * (8 * work))%N by ring.
      apply N.mul_le_mono_l.
      eapply N.le_trans; [exact HmapsN|].
      apply N.mul_le_mono_l. exact Hbase_work. }
    assert (Hcoefficient : (M.c_map * (64 * (M.c_map + 1) + 1) +
      16 * M.c_map * (128 * (M.c_map + 1) + 1) + 4 <=
      4096 * (M.c_map + 1) * (M.c_map + 1))%N) by nia.
    pose proof (N.mul_le_mono_r _ _ work Hcoefficient) as Hbudget.
    rewrite !N.mul_add_distr_r in Hbudget.
    pose proof (Std.Datatypes.T_fst_le unaries) as Hfst.
    pose proof (Std.Datatypes.T_snd_le unaries) as Hsnd.
    unfold T_strengthen. time_simpl. fold unaries.
    match goal with
    | |- context [M.T_fold ?step ?callback m ?seed] =>
      assert (Hfold_actual : (M.T_fold step callback m seed <=
        M.c_map * (64 * (M.c_map + 1) + 1) * work)%N) by exact Hfold';
      set (fold_cost := M.T_fold step callback m seed) in *
    end.
    match goal with
    | |- context [M.T_merge ?step ?callback m ?right] =>
      assert (Hmerge_actual : (M.T_merge step callback m right <=
        16 * M.c_map * (128 * (M.c_map + 1) + 1) * work)%N) by exact Hmerge';
      set (merge_cost := M.T_merge step callback m right) in *
    end.
    clearbody work fold_cost merge_cost.
    clear - Hfold_actual Hmerge_actual Hfst Hsnd Hpositive Hbudget. lia.
  Qed.

  Lemma T3_strengthen : forall m, dbm_wf m ->
    (T_strengthen m <= k_octagon * N.of_nat ((supp m + 1)^2 * (b m + ell m + 1)))%N.
  Proof.
    intros m Hwf. pose proof (T_strengthen_small m) as Hclock.
    pose proof (weight_le m Hwf) as Hweight.
    assert (Hwork : strengthening_work m <=
      3 * ((supp m + 1)^2 * (b m + ell m + 1))).
    { unfold strengthening_work. cbn [Nat.pow]. nia. }
    pose proof (time_of_nat_le _ _ Hwork) as Hcast. rewrite Nat2N.inj_mul in Hcast.
    eapply N.le_trans; [exact Hclock|].
    eapply N.le_trans; [apply N.mul_le_mono_l; exact Hcast|].
    replace (4096 * (M.c_map + 1) * (M.c_map + 1) *
      (N.of_nat 3 * N.of_nat ((supp m + 1)^2 * (b m + ell m + 1))))%N with
      ((4096 * (M.c_map + 1) * (M.c_map + 1) * 3) *
        N.of_nat ((supp m + 1)^2 * (b m + ell m + 1)))%N by (cbn [N.of_nat]; ring).
    apply N.mul_le_mono_r. unfold k_octagon. nia.
  Qed.


  (** This private coefficient is the raw round allowance, before closure composition. *)
  Definition fw_round_factor : N := (1024 * (M.c_map + 1) * (M.c_map + 1))%N.

  (** Early exit records no more rounds than the supplied pivot list. *)
  Lemma fw_trace_length : forall ks m, length (fw_trace ks m) <= length ks.
  Proof.
    intro ks. induction ks as [|k ks IH]; intro m.
    - cbn [fw_trace length]. lia.
    - rewrite fw_trace_nonnegative. cbn [length].
      destruct (nonnegative k (fw_round k m)); cbn [length].
      + pose proof (IH (fw_round k m)). lia.
      + lia.
  Qed.

  (** Traced keys come from the pivot list and every traced matrix retains raw support sizes. *)
  Lemma fw_trace_resources : forall ks m k a, In (k, a) (fw_trace ks m) ->
    In k ks /\ supp a = supp m /\ b a = b m.
  Proof.
    intro ks. induction ks as [|p ks IH]; intros m k a Hin.
    - contradiction.
    - rewrite fw_trace_nonnegative in Hin. cbn [In] in Hin.
      destruct Hin as [Heq|Hin].
      + injection Heq as Hkey Hstate. subst k a. split; [now left|]. now split.
      + destruct (nonnegative p (fw_round p m)); [|contradiction].
        destruct (IH (fw_round p m) k a Hin) as [Hkey [Hsupport Hbits]].
        destruct (supp_fw_round p m) as [Hround_support Hround_bits].
        split; [now right|]. split; congruence.
  Qed.

  (** At most one support-sized family of quadratic allowances fits a cubic allowance. *)
  Lemma quadratic_cubic_budget : forall n count payload, count <= n + 1 ->
    ((n + 1)^2 * payload) * count <= (n + 1)^3 * payload.
  Proof.
    intros n count payload Hcount.
    replace (((n + 1)^2 * payload) * count) with
      ((count * (n + 1)^2) * payload) by ring.
    apply Nat.mul_le_mono_r.
    change (count * (n + 1)^2 <= (n + 1) * (n + 1)^2).
    now apply Nat.mul_le_mono_r.
  Qed.

  (** Preserved support and logarithmic entry growth bound every performed round uniformly. *)
  Lemma traced_round_time_le : forall m k a, dbm_wf m ->
    In (k, a) (fw_trace (keys m) m) ->
    (T_fw_round k a <= 2 * fw_round_factor * N.of_nat
      ((supp m + 1)^2 * (b m + ell m + Nat.log2 (supp m) + 1)))%N.
  Proof.
    intros m k a Hwf Hin.
    destruct (fw_trace_resources (keys m) m k a Hin) as [Hkey [Hsupport Hbits]].
    assert (Hkey_bits : K.bits k <= b m).
    { unfold K.bits. apply support_bits. now apply keys_support. }
    pose proof (bits_fw_trace_le (keys m) m k a Hwf Hin) as Hell.
    eapply N.le_trans; [apply T_fw_round_raw|].
    replace (2 * fw_round_factor * N.of_nat
      ((supp m + 1)^2 * (b m + ell m + Nat.log2 (supp m) + 1)))%N with
      (fw_round_factor * (2 * N.of_nat
        ((supp m + 1)^2 * (b m + ell m + Nat.log2 (supp m) + 1))))%N by ring.
    apply N.mul_le_mono_l.
    replace (2 * N.of_nat
      ((supp m + 1)^2 * (b m + ell m + Nat.log2 (supp m) + 1)))%N with
      (N.of_nat (2 * ((supp m + 1)^2 *
        (b m + ell m + Nat.log2 (supp m) + 1))))
      by (rewrite Nat2N.inj_mul; reflexivity).
    apply time_of_nat_le. rewrite Hsupport, Hbits.
    replace (2 * ((supp m + 1)^2 * (b m + ell m + Nat.log2 (supp m) + 1))) with
      ((supp m + 1)^2 * (2 * (b m + ell m + Nat.log2 (supp m) + 1))) by ring.
    apply Nat.mul_le_mono_l. lia.
  Qed.

  (** Summing the performed rounds needs only one additional factor of support size. *)
  Lemma trace_cost_cubic : forall m, dbm_wf m ->
    (trace_cost (keys m) m <= 2 * fw_round_factor * N.of_nat
      ((supp m + 1)^3 * (b m + ell m + Nat.log2 (supp m) + 1)))%N.
  Proof.
    intros m Hwf.
    set (xs := fw_trace (keys m) m).
    set (units := (supp m + 1)^2 * (b m + ell m + Nat.log2 (supp m) + 1)).
    assert (Hpoint : forall km, In km xs ->
      (T_fw_round (fst km) (snd km) <= 2 * fw_round_factor * N.of_nat units)%N).
    { intros [k a] Hin. cbn [fst snd]. unfold units.
      unfold xs in Hin. now apply traced_round_time_le. }
    assert (Hsum : (fold_right N.add 0%N
      (map (fun km => T_fw_round (fst km) (snd km)) xs) <=
      (2 * fw_round_factor * N.of_nat units) * N.of_nat (length xs))%N).
    { pose proof (time_sum_bound (K.t * dbm) xs
        (fun km => T_fw_round (fst km) (snd km)) (fun _ => 1%nat)
        (2 * fw_round_factor * N.of_nat units)%N) as Hbound.
      assert (Hcallback : forall km, In km xs ->
        (T_fw_round (fst km) (snd km) <=
          (2 * fw_round_factor * N.of_nat units) * N.of_nat 1)%N).
      { intros km Hin. change (T_fw_round (fst km) (snd km) <=
          (2 * fw_round_factor * N.of_nat units) * 1)%N.
        rewrite N.mul_1_r. now apply Hpoint. }
      specialize (Hbound Hcallback). now rewrite sum_weight_one in Hbound. }
    assert (Hlength : length xs <= supp m).
    { unfold xs. eapply Nat.le_trans; [apply fw_trace_length|]. now apply keys_le. }
    assert (Hunits : units * length xs <=
      (supp m + 1)^3 * (b m + ell m + Nat.log2 (supp m) + 1)).
    { unfold units. apply quadratic_cubic_budget. lia. }
    pose proof (time_of_nat_le _ _ Hunits) as Hcast.
    rewrite (Nat2N.inj_mul units (length xs)) in Hcast.
    unfold trace_cost. fold xs.
    eapply N.le_trans; [exact Hsum|].
    replace ((2 * fw_round_factor * N.of_nat units) * N.of_nat (length xs))%N with
      (2 * fw_round_factor * (N.of_nat units * N.of_nat (length xs)))%N by ring.
    now apply N.mul_le_mono_l.
  Qed.

  (** The public closure coefficient covers round updates and additive traversal overhead. *)
  Lemma k_octagon_closure_coefficient :
    (2 * fw_round_factor + 128 * (M.c_map + 1) <= k_octagon)%N.
  Proof.
    unfold fw_round_factor, k_octagon. nia.
  Qed.

  (** Floyd-Warshall has cubic support work with logarithmic entry-bit growth. *)
  Lemma T1_fw : forall m, dbm_wf m ->
    (T_fw m <= k_octagon * N.of_nat
      ((supp m + 1)^3 * (b m + ell m + Nat.log2 (supp m) + 1)))%N.
  Proof.
    intros m Hwf.
    pose proof (T_fw_additive m Hwf) as Htime.
    pose proof (trace_cost_cubic m Hwf) as Htrace.
    set (work := N.of_nat ((supp m + 1)^3 *
      (b m + ell m + Nat.log2 (supp m) + 1))) in *.
    assert (Hinitial_nat : (supp m + 1)^2 * (b m + ell m + 1) <=
      (supp m + 1)^3 * (b m + ell m + Nat.log2 (supp m) + 1)).
    { eapply Nat.le_trans with
        ((supp m + 1)^2 * (b m + ell m + Nat.log2 (supp m) + 1)).
      - apply Nat.mul_le_mono_l. lia.
      - pose proof (quadratic_cubic_budget (supp m) 1
          (b m + ell m + Nat.log2 (supp m) + 1) ltac:(lia)) as Hdegree.
        now rewrite Nat.mul_1_r in Hdegree. }
    pose proof (time_of_nat_le _ _ Hinitial_nat) as Hinitial.
    change (N.of_nat ((supp m + 1)^2 * (b m + ell m + 1)) <= work)%N in Hinitial.
    pose proof (N.mul_le_mono_l _ _ (128 * (M.c_map + 1))%N Hinitial) as Hframe.
    pose proof (N.mul_le_mono_r _ _ work k_octagon_closure_coefficient) as Hbudget.
    rewrite N.mul_add_distr_r in Hbudget.
    set (initial_work := N.of_nat ((supp m + 1)^2 * (b m + ell m + 1))) in *.
    clear Hinitial_nat Hinitial. clearbody work initial_work. lia.
  Qed.

  (** A supported normalization stage fits the original cubic budget. *)
  Lemma tclose_stage_work : forall m state extra,
    supp state = supp m ->
    b state = b m ->
    ell state <= ell m + Nat.log2 (supp m) + extra ->
    (supp state + 1)^2 * (b state + ell state + 1) <=
      (extra + 1) * ((supp m + 1)^3 *
        (b m + ell m + Nat.log2 (supp m) + 1)).
  Proof.
    intros m state extra Hcount Hkeys Hentries.
    set (payload := b m + ell m + Nat.log2 (supp m) + 1).
    assert (Hpositive : 1 <= payload) by (unfold payload; lia).
    assert (Hextra : extra <= extra * payload).
    { replace extra with (extra * 1) at 1 by ring.
      apply Nat.mul_le_mono_l. exact Hpositive. }
    assert (Hentry : b m + ell state + 1 <= payload + extra)
      by (unfold payload; lia).
    assert (Hdegree : (supp m + 1)^2 <= (supp m + 1)^3).
    { change ((supp m + 1)^2 <= (supp m + 1) * (supp m + 1)^2).
      replace ((supp m + 1)^2) with (1 * (supp m + 1)^2) at 1 by ring.
      apply Nat.mul_le_mono_r. lia. }
    rewrite Hcount, Hkeys. fold payload.
    eapply Nat.le_trans with ((supp m + 1)^2 * ((extra + 1) * payload)).
    - apply Nat.mul_le_mono_l.
      replace ((extra + 1) * payload) with (payload + extra * payload) by ring. lia.
    - replace ((supp m + 1)^2 * ((extra + 1) * payload)) with
        ((extra + 1) * ((supp m + 1)^2 * payload)) by ring.
      apply Nat.mul_le_mono_l, Nat.mul_le_mono_r. exact Hdegree.
  Qed.

  (** Floyd, tightening, strengthening, and diagonal scans share one cubic allowance. *)
  Lemma T_tclose_le : forall m, dbm_wf m ->
    (T_tclose m <= c_octagon * N.of_nat (((supp m + 1)^3)%nat) *
    N.of_nat ((b m + ell m + Nat.log2 (supp m) + 1)%nat))%N.
  Proof.
    intros m Hwf.
    set (units := (supp m + 1)^3 * (b m + ell m + Nat.log2 (supp m) + 1)).
    set (work := N.of_nat units).
    replace (c_octagon * N.of_nat ((supp m + 1)^3) *
      N.of_nat (b m + ell m + Nat.log2 (supp m) + 1))%N with
      (c_octagon * work)%N by (unfold work, units; rewrite Nat2N.inj_mul; ring).
    destruct (fw_sizes m) as [Hfwn Hfwb].
    pose proof (fw_bits m Hwf) as Hfwe.
    destruct (support_sizes (tighten (fw m)) (fw m) (support_tighten (fw m)))
      as [Hroundn Hroundb].
    pose proof (bits_tighten_le (fw m)) as Hrounde.
    assert (Hinitial_nat : (supp m + 1)^2 * (b m + ell m + 1) <= units).
    { pose proof (tclose_stage_work m m 0 eq_refl eq_refl ltac:(lia)) as Hbound.
      change ((supp m + 1)^2 * (b m + ell m + 1) <= 1 * units) in Hbound.
      now rewrite Nat.mul_1_l in Hbound. }
    assert (Hclosed_nat : (supp (fw m) + 1)^2 * (b (fw m) + ell (fw m) + 1) <=
      3 * units).
    { exact (tclose_stage_work m (fw m) 2 Hfwn Hfwb Hfwe). }
    assert (Hrounded_nat :
      (supp (tighten (fw m)) + 1)^2 *
        (b (tighten (fw m)) + ell (tighten (fw m)) + 1) <= 4 * units).
    { apply (tclose_stage_work m (tighten (fw m)) 3); lia. }
    pose proof (time_of_nat_le _ _ Hinitial_nat) as Hinitial.
    change (N.of_nat ((supp m + 1)^2 * (b m + ell m + 1)) <= work)%N in Hinitial.
    pose proof (time_of_nat_le _ _ Hclosed_nat) as Hclosed.
    rewrite (Nat2N.inj_mul 3 units) in Hclosed.
    change (N.of_nat ((supp (fw m) + 1)^2 * (b (fw m) + ell (fw m) + 1)) <=
      3 * work)%N in Hclosed.
    pose proof (time_of_nat_le _ _ Hrounded_nat) as Hrounded.
    rewrite (Nat2N.inj_mul 4 units) in Hrounded.
    change (N.of_nat ((supp (tighten (fw m)) + 1)^2 *
      (b (tighten (fw m)) + ell (tighten (fw m)) + 1)) <= 4 * work)%N in Hrounded.
    pose proof (T1_fw m Hwf) as Hfw.
    change (T_fw m <= k_octagon * work)%N in Hfw.
    assert (Hframe : (k_octagon * N.of_nat ((supp m + 1)^2 * (b m + ell m + 1)) <=
      k_octagon * work)%N) by (now apply N.mul_le_mono_l).
    assert (Htighten : (T_tighten (fw m) <= 3 * (k_octagon * work))%N).
    { eapply N.le_trans; [apply T2_tighten, wf_fw; exact Hwf|].
      replace (3 * (k_octagon * work))%N with (k_octagon * (3 * work))%N by ring.
      now apply N.mul_le_mono_l. }
    assert (Hstrengthen : (T_strengthen (tighten (fw m)) <= 4 * (k_octagon * work))%N).
    { eapply N.le_trans; [apply T3_strengthen, wf_tighten, wf_fw; exact Hwf|].
      replace (4 * (k_octagon * work))%N with (k_octagon * (4 * work))%N by ring.
      now apply N.mul_le_mono_l. }
    assert (Hcoefficient : (9 * k_octagon <= c_octagon)%N)
      by (unfold k_octagon, c_octagon; nia).
    pose proof (N.mul_le_mono_r _ _ work Hcoefficient) as Hbudget.
    replace (9 * k_octagon * work)%N with (9 * (k_octagon * work))%N in Hbudget by ring.
    pose proof (T4_tclose m Hwf) as Hclock.
    set (charge := (k_octagon * work)%N) in *.
    assert (Hstages : ((if diag_ok (fw m)
      then T_tighten (fw m) + T_strengthen (tighten (fw m)) else 0) <= 7 * charge)%N).
    { destruct (diag_ok (fw m)); lia. }
    clear Hfwn Hfwb Hfwe Hroundn Hroundb Hrounde Hinitial_nat Hclosed_nat Hrounded_nat
      Hinitial Hclosed Hrounded Hcoefficient.
    clearbody charge work. clear units.
    lia.
  Qed.

(** A merge can introduce only a code that was present in one of its inputs. *)
  Lemma codes_merge_length : forall (A B C : Type)
      (f : option A -> option B -> option C) ma mb,
    f None None = None ->
    length (M.codes (M.merge f ma mb)) <= length (M.codes ma) + length (M.codes mb).
  Proof.
    intros A B C f ma mb Hnone.
    assert (Hincl : incl (M.codes (M.merge f ma mb)) (M.codes ma ++ M.codes mb)).
    { intros p Hp. apply in_app_iff. apply M.codes_spec in Hp.
      rewrite M.find_merge in Hp by exact Hnone.
      destruct (M.find p ma) as [a|] eqn:Ha.
      - left. apply M.codes_spec. congruence.
      - right. apply M.codes_spec. intro Hb. rewrite Hb, Hnone in Hp. contradiction. }
    pose proof (NoDup_incl_length (M.codes_nodup C (M.merge f ma mb)) Hincl) as Hlength.
    now rewrite length_app in Hlength.
  Qed.

  Lemma code_work_zero_merge : forall (A B C : Type)
      (f : option A -> option B -> option C) ma mb,
    f None None = None ->
    code_work (fun _ => 0) (M.merge f ma mb) <=
      code_work (fun _ => 0) ma + code_work (fun _ => 0) mb.
  Proof.
    intros A B C f ma mb Hnone. rewrite !code_work_zero.
    pose proof (M.nodes_merge A B C f ma mb).
    pose proof (codes_merge_length A B C f ma mb Hnone). lia.
  Qed.

  Lemma code_work_zero_relax : forall prefix row exit,
    code_work (fun _ : Z => 0%nat) (relax_row prefix row exit) <=
      code_work (fun _ : Z => 0%nat) row + code_work (fun _ : Z => 0%nat) exit.
  Proof.
    intros [a|] row exit; [apply code_work_zero_merge; reflexivity|].
    cbn [relax_row]. lia.
  Qed.

  Local Definition optional_bits (a : option Z) : nat := option_weight Z.size_nat a.

  Local Definition relaxation_work (prefix : option Z) (exit : M.t Z) : nat :=
    option_weight (fun a => code_work (fun z => (Z.size_nat a + Z.size_nat z + 1)%nat) exit) prefix.

  (** A sparse row relaxation charges the prefix only at finite exit bindings. *)
  Lemma T_relax_row_le : forall prefix row exit,
    (T_relax_row prefix row exit <= 32 * (M.c_map + 1) *
      N.of_nat (code_work (fun _ : Z => 0%nat) row + relaxation_work prefix exit + 1))%N.
  Proof.
    intros [a|] row exit.
    - assert (Hcallback : forall old next,
        (T_via_bound a old next <= 8 * N.of_nat
          (option_weight (fun _ : Z => 0%nat) old +
           option_weight (fun z => (Z.size_nat a + Z.size_nat z + 1)%nat) next + 1))%N).
      { intros old next. rewrite option_weight_zero. apply T_via_bound_le. }
      pose proof (T_merge_code_work Z Z Z (via_bound a)
        (fun x y => T_via_bound a x y) (fun _ => 0)
        (fun z => (Z.size_nat a + Z.size_nat z + 1)%nat) row exit 8%N Hcallback) as Hmerge.
      cbn [relaxation_work option_weight].
      set (work := N.of_nat (code_work (fun _ : Z => 0%nat) row +
        code_work (fun z => (Z.size_nat a + Z.size_nat z + 1)%nat) exit + 1)) in *.
      assert (Hpositive : (1 <= work)%N) by (unfold work; lia).
      assert (Hcoefficient : (M.c_map * (8 + 1) * 2 + 1 <= 32 * (M.c_map + 1))%N) by nia.
      pose proof (N.mul_le_mono_r _ _ work Hcoefficient) as Hbudget.
      rewrite N.mul_add_distr_r, N.mul_1_l in Hbudget.
      unfold T_relax_row. cbn beta iota zeta.
      match goal with
      | |- context [M.T_merge ?step ?callback row exit] =>
        assert (Hmerge_actual : (M.T_merge step callback row exit <=
          M.c_map * (8 + 1) * 2 * work)%N) by exact Hmerge;
        set (merge_cost := M.T_merge step callback row exit) in *
      end.
      clearbody work merge_cost. clear - Hmerge_actual Hpositive Hbudget. lia.
    - unfold T_relax_row, relaxation_work, option_weight. cbn beta iota zeta.
      rewrite !Nat2N.inj_add. nia.
  Qed.

  Lemma T_edge_prefix_le : forall d a,
    (T_edge_prefix d a <= 8 * N.of_nat (optional_bits a + Z.size_nat d + 1))%N.
  Proof.
    intros d [a|]; unfold optional_bits; cbn [option_weight]; time_step.
  Qed.

  Lemma T_twin_prefix_le : forall d a cross,
    (T_twin_prefix d a cross <=
      64 * N.of_nat (optional_bits a + optional_bits cross + Z.size_nat d + 1))%N.
  Proof.
    intros d [a|] [c|]; unfold optional_bits; cbn [option_weight].
    - pose proof (zbits_add_sum a d).
      pose proof (zbits_add_sum (a + d)%Z c).
      unfold T_twin_prefix. time_simpl. time_pose.
      rewrite ?Nat2N.inj_add in *. nia.
    - time_step.
    - time_step.
    - time_step.
  Qed.

  Local Definition increment_row_work (i j : K.t) (d : Z)
      (exit1 exit2 : M.t Z) (cross1 cross2 : option Z) (row : M.t Z) : nat :=
    K.bits i + K.bits j + Z.size_nat d +
    optional_bits cross1 + optional_bits cross2 +
    optional_bits (M.get i row) + optional_bits (M.get (flip j) row) +
    code_work (fun _ : Z => 0%nat) row +
    code_work (fun _ : Z => 0%nat) exit1 + code_work (fun _ : Z => 0%nat) exit2 +
    relaxation_work (edge_prefix d (M.get i row)) exit1 +
    relaxation_work (edge_prefix d (M.get (flip j) row)) exit2 +
    relaxation_work (twin_prefix d (M.get i row) cross1) exit2 +
    relaxation_work (twin_prefix d (M.get (flip j) row) cross2) exit1 + 1.

(** Four sparse relaxations share the source lookups and charge their intermediate skeletons. *)
  Lemma T_increment_row_le : forall i j d exit1 exit2 cross1 cross2 old ignored,
    (T_increment_row i j d exit1 exit2 cross1 cross2 old ignored <=
      512 * (M.c_map + 1) * N.of_nat
        (option_weight (increment_row_work i j d exit1 exit2 cross1 cross2) old + 1))%N.
  Proof.
    intros i j d exit1 exit2 cross1 cross2 [row|] ignored; [|time_step].
    cbn [option_weight].
    set (a := M.get i row).
    set (bprefix := M.get (flip j) row).
    set (r1 := relax_row (edge_prefix d a) row exit1).
    set (r2 := relax_row (edge_prefix d bprefix) r1 exit2).
    set (r3 := relax_row (twin_prefix d a cross1) r2 exit2).
    set (units := increment_row_work i j d exit1 exit2 cross1 cross2 row + 1).
    set (work := N.of_nat units).
    assert (Hpositive : (1 <= work)%N) by (unfold work, units; lia).
    pose proof (code_work_zero_relax (edge_prefix d a) row exit1) as Hr1.
    fold r1 in Hr1.
    pose proof (code_work_zero_relax (edge_prefix d bprefix) r1 exit2) as Hr2.
    fold r2 in Hr2.
    pose proof (code_work_zero_relax (twin_prefix d a cross1) r2 exit2) as Hr3.
    fold r3 in Hr3.
    assert (Hrelax : forall prefix source exit,
      code_work (fun _ : Z => 0%nat) source + relaxation_work prefix exit + 1 <= 2 * units ->
      (T_relax_row prefix source exit <= 64 * (M.c_map + 1) * work)%N).
    { intros prefix source exit Hunits. eapply N.le_trans; [apply T_relax_row_le|].
      replace (64 * (M.c_map + 1) * work)%N with
        (32 * (M.c_map + 1) * (2 * work))%N by ring.
      apply N.mul_le_mono_l. unfold work.
      pose proof (time_of_nat_le _ _ Hunits) as Hcast. now rewrite Nat2N.inj_mul in Hcast. }
    assert (Hrelax1 : (T_relax_row (edge_prefix d a) row exit1 <=
      64 * (M.c_map + 1) * work)%N).
    { apply Hrelax. unfold units, increment_row_work. fold a bprefix. lia. }
    assert (Hrelax2 : (T_relax_row (edge_prefix d bprefix) r1 exit2 <=
      64 * (M.c_map + 1) * work)%N).
    { apply Hrelax. unfold units, increment_row_work. fold a bprefix. lia. }
    assert (Hrelax3 : (T_relax_row (twin_prefix d a cross1) r2 exit2 <=
      64 * (M.c_map + 1) * work)%N).
    { apply Hrelax. unfold units, increment_row_work. fold a bprefix. lia. }
    assert (Hrelax4 : (T_relax_row (twin_prefix d bprefix cross2) r3 exit1 <=
      64 * (M.c_map + 1) * work)%N).
    { apply Hrelax. unfold units, increment_row_work. fold a bprefix. lia. }
    assert (Hedge : forall prefix, optional_bits prefix + Z.size_nat d + 1 <= units ->
      (T_edge_prefix d prefix <= 8 * work)%N).
    { intros prefix Hunits. eapply N.le_trans; [apply T_edge_prefix_le|].
      apply N.mul_le_mono_l. unfold work. now apply time_of_nat_le. }
    assert (Hedge1 : (T_edge_prefix d a <= 8 * work)%N).
    { apply Hedge. unfold units, increment_row_work. fold a bprefix. lia. }
    assert (Hedge2 : (T_edge_prefix d bprefix <= 8 * work)%N).
    { apply Hedge. unfold units, increment_row_work. fold a bprefix. lia. }
    assert (Htwin : forall prefix cross,
      optional_bits prefix + optional_bits cross + Z.size_nat d + 1 <= units ->
      (T_twin_prefix d prefix cross <= 64 * work)%N).
    { intros prefix cross Hunits. eapply N.le_trans; [apply T_twin_prefix_le|].
      apply N.mul_le_mono_l. unfold work. now apply time_of_nat_le. }
    assert (Htwin1 : (T_twin_prefix d a cross1 <= 64 * work)%N).
    { apply Htwin. unfold units, increment_row_work. fold a bprefix. lia. }
    assert (Htwin2 : (T_twin_prefix d bprefix cross2 <= 64 * work)%N).
    { apply Htwin. unfold units, increment_row_work. fold a bprefix. lia. }
    assert (Hget : forall k, K.bits k + 1 <= 2 * units ->
      (M.T_get k row <= 2 * M.c_map * work)%N).
    { intros k Hunits. eapply N.le_trans; [apply M.T_get_le|].
      replace (2 * M.c_map * work)%N with (M.c_map * (2 * work))%N by ring.
      apply N.mul_le_mono_l. unfold work.
      pose proof (time_of_nat_le _ _ Hunits) as Hcast. now rewrite Nat2N.inj_mul in Hcast. }
    assert (Hgeti : (M.T_get i row <= 2 * M.c_map * work)%N).
    { apply Hget. unfold units, increment_row_work. lia. }
    assert (Hgetj : (M.T_get (flip j) row <= 2 * M.c_map * work)%N).
    { apply Hget. pose proof (flip_bits j). unfold units, increment_row_work. lia. }
    pose proof (T_flip_le j) as Hflip.
    assert (Hcoefficient : (256 * (M.c_map + 1) + 4 * M.c_map + 160 <=
      512 * (M.c_map + 1))%N) by nia.
    pose proof (N.mul_le_mono_r _ _ work Hcoefficient) as Hbudget.
    repeat rewrite N.mul_add_distr_r in Hbudget.
    clear Hrelax Hedge Htwin Hget Hcoefficient Hr1 Hr2 Hr3.
    change (T_increment_row i j d exit1 exit2 cross1 cross2 (Some row) ignored <=
      512 * (M.c_map + 1) * work)%N.
    clearbody work. clear units.
    unfold T_increment_row. cbn beta iota zeta. fold a bprefix r1 r2 r3. lia.
  Qed.

Lemma optional_bits_bound : forall upper a,
    bound_bits upper a -> optional_bits a <= upper.
  Proof.
    intros upper [a|] Hbits; unfold optional_bits; cbn [option_weight].
    - now apply Hbits.
    - lia.
  Qed.

  Lemma code_work_zero_support : forall m row,
    (forall p, In p (M.codes row) -> In p (support m)) ->
    code_work (fun _ : Z => 0%nat) row <= supp m * (b m + 2).
  Proof.
    intros m row Hsupport. rewrite code_work_zero.
    pose proof (nodes_support Z row m Hsupport).
    pose proof (codes_support_length Z row m Hsupport). nia.
  Qed.

  Lemma relaxation_work_bound : forall m row prefix upper,
    (forall p, In p (M.codes row) -> In p (support m)) ->
    (forall p z, M.find p row = Some z -> Z.size_nat z <= ell m) ->
    bound_bits upper prefix ->
    relaxation_work prefix row <= supp m * (b m + ell m + upper + 3).
  Proof.
    intros m row [a|] upper Hsupport Hbits Hprefix; cbn [relaxation_work option_weight].
    - pose proof (Hprefix a eq_refl) as Ha.
      eapply Nat.le_trans; [apply code_work_bits_bound; eassumption|].
      apply Nat.mul_le_mono_l. lia.
    - lia.
  Qed.

  (** Each signed callback charges its original row and four supported suffix rows. *)
  Lemma increment_row_work_bound : forall m i j d row, In row (rows m) ->
    increment_row_work i j d (row_of (M.get j m)) (row_of (M.get (flip i) m))
      (entry m j (flip j)) (entry m (flip i) i) row <=
      M.nodes row + K.bits i + K.bits j + Z.size_nat d + 4 * ell m + 1 +
      supp m * (6 * b m + 8 * ell m + 4 * Z.size_nat d + 25).
  Proof.
    intros m i j d row Hin.
    assert (Hsupport : forall q, In q (M.codes row) -> In q (support m)).
    { intros q Hq. apply support_spec. right. apply in_flat_map. exists row. now split. }
    pose proof (codes_support_length Z row m Hsupport) as Hcount.
    apply rows_find in Hin. destruct Hin as [p Hrow].
    assert (Hget : forall k, bound_bits (ell m) (M.get k row)).
    { intros k a Ha. exact (row_get_bits m p row k a Hrow Ha). }
    assert (Hentry : forall x y, bound_bits (ell m) (entry m x y)).
    { intros x y a Ha. apply (ell_entry m (K.encode x) (K.encode y) a).
      now rewrite raw_entry_get. }
    pose proof (optional_bits_bound (ell m) (M.get i row) (Hget i)) as Ha.
    pose proof (optional_bits_bound (ell m) (M.get (flip j) row) (Hget (flip j))) as Hb.
    pose proof (optional_bits_bound (ell m) (entry m j (flip j)) (Hentry j (flip j))) as Hc1.
    pose proof (optional_bits_bound (ell m) (entry m (flip i) i) (Hentry (flip i) i)) as Hc2.
    assert (Hupper : forall a, bound_bits (ell m) a ->
      bound_bits (ell m + Z.size_nat d) a).
    { intros a Hbits z Hz. pose proof (Hbits z Hz). lia. }
    assert (Hedge : forall a, bound_bits (ell m) a ->
      bound_bits (ell m + Z.size_nat d + 2) (edge_prefix d a)).
    { intros a Hbits. apply edge_prefix_bits; [lia|now apply Hupper]. }
    assert (Htwin : forall a c, bound_bits (ell m) a -> bound_bits (ell m) c ->
      bound_bits (ell m + Z.size_nat d + 2) (twin_prefix d a c)).
    { intros a c Hbits Hcross. apply twin_prefix_bits; [lia|now apply Hupper|now apply Hupper]. }
    assert (Hexit : forall k prefix, bound_bits (ell m + Z.size_nat d + 2) prefix ->
      relaxation_work prefix (row_of (M.get k m)) <=
      supp m * (b m + 2 * ell m + Z.size_nat d + 5)).
    { intros k prefix Hbits. eapply Nat.le_trans.
      - apply (relaxation_work_bound m (row_of (M.get k m)) prefix
          (ell m + Z.size_nat d + 2)); [apply row_lookup_support|apply row_lookup_bits|exact Hbits].
      - apply Nat.mul_le_mono_l. lia. }
    pose proof (Hexit j (edge_prefix d (M.get i row)) (Hedge _ (Hget i))) as Hr1.
    pose proof (Hexit (flip i) (edge_prefix d (M.get (flip j) row))
      (Hedge _ (Hget (flip j)))) as Hr2.
    pose proof (Hexit (flip i) (twin_prefix d (M.get i row) (entry m j (flip j)))
      (Htwin _ _ (Hget i) (Hentry j (flip j)))) as Hr3.
    pose proof (Hexit j (twin_prefix d (M.get (flip j) row) (entry m (flip i) i))
      (Htwin _ _ (Hget (flip j)) (Hentry (flip i) i))) as Hr4.
    pose proof (code_work_zero_support m (row_of (M.get j m)) (row_lookup_support m j)) as He1.
    pose proof (code_work_zero_support m (row_of (M.get (flip i) m))
      (row_lookup_support m (flip i))) as He2.
    unfold increment_row_work. rewrite (code_work_zero Z row).
    clear Hentry Hget Hupper Hedge Htwin Hexit Hrow Hsupport. nia.
  Qed.

  Lemma increment_scalar_work_bound : forall n bb ki kj ee dd,
    ki + kj + dd + 4 * ee + 1 + n * (6 * bb + 8 * ee + 4 * dd + 25) <=
      32 * (n + 1) * (bb + ki + kj + ee + dd + 1).
  Proof.
    intros n bb ki kj ee dd. nia.
  Qed.

  Lemma increment_budget_composition : forall (nodes count total row_nodes row_cost units : nat),
    count <= units ->
    nodes + row_nodes <= units ->
    total <= row_nodes + row_cost ->
    row_cost <= 32 * units ->
    nodes + count + total <= 34 * units.
  Proof.
    intros nodes count total row_nodes row_cost units Hcount Hnodes Htotal Hrows. lia.
  Qed.

  Lemma increment_matrix_work_bound : forall m i j d,
    code_work (increment_row_work i j d
      (row_of (M.get j m)) (row_of (M.get (flip i) m))
      (entry m j (flip j)) (entry m (flip i) i)) m <=
      34 * (supp m + 1)^2 * (b m + K.bits i + K.bits j + ell m + Z.size_nat d + 1).
  Proof.
    intros m i j d.
    set (rowwork := increment_row_work i j d
      (row_of (M.get j m)) (row_of (M.get (flip i) m))
      (entry m j (flip j)) (entry m (flip i) i)).
    set (allowance := K.bits i + K.bits j + Z.size_nat d + 4 * ell m + 1 +
      supp m * (6 * b m + 8 * ell m + 4 * Z.size_nat d + 25)).
    assert (Hcount : length (M.codes m) <= supp m).
    { apply codes_support_length. intros p Hp. apply support_spec. now left. }
    pose proof (rows_length m) as Hrows.
    assert (Hsum : sum_weight rowwork (rows m) <=
      sum_weight (fun row => M.nodes row + allowance) (rows m)).
    { apply sum_weight_mono. intros row Hin. unfold rowwork.
      eapply Nat.le_trans; [exact (increment_row_work_bound m i j d row Hin)|].
      unfold allowance. clear -m i j d row. lia. }
    rewrite (sum_weight_add (M.t Z) M.nodes (fun _ => allowance) (rows m)),
      (sum_weight_const (M.t Z) (rows m) allowance) in Hsum.
    change (sum_weight rowwork (rows m) <=
      sum_weight M.nodes (rows m) + length (rows m) * allowance) in Hsum.
    assert (Hprod : length (rows m) * allowance <= supp m * allowance).
    { apply Nat.mul_le_mono_r. lia. }
    pose proof (skel_le m) as Hskel.
    change (M.nodes m + sum_weight M.nodes (rows m) <=
      (supp m + 1)^2 * (b m + 1)) in Hskel.
    unfold code_work at 1. rewrite (stored_weight_rows rowwork m).
    set (units := (supp m + 1)^2 * (b m + K.bits i + K.bits j + ell m + Z.size_nat d + 1)).
    replace (34 * (supp m + 1)^2 * (b m + K.bits i + K.bits j + ell m + Z.size_nat d + 1))
      with (34 * units) by (unfold units; ring).
    assert (Hcount_units : supp m <= units).
    { unfold units. apply quadratic_work_count. clear -m i j d. lia. }
    assert (Hskel_units : M.nodes m + sum_weight M.nodes (rows m) <= units).
    { eapply Nat.le_trans; [exact Hskel|]. unfold units. apply Nat.mul_le_mono_l.
      clear -m i j d. lia. }
    assert (Hprod_units : length (rows m) * allowance <= 32 * units).
    { eapply Nat.le_trans; [exact Hprod|]. unfold units.
      replace (32 * ((supp m + 1)^2 *
        (b m + K.bits i + K.bits j + ell m + Z.size_nat d + 1))) with
        (32 * (supp m + 1)^2 * (b m + K.bits i + K.bits j + ell m + Z.size_nat d + 1)) by ring.
      apply quadratic_work_rows. unfold allowance. apply increment_scalar_work_bound. }
    fold rowwork.
    apply (increment_budget_composition (M.nodes m) (length (M.codes m))
      (sum_weight rowwork (rows m)) (sum_weight M.nodes (rows m))
      (length (rows m) * allowance) units).
    - exact (Nat.le_trans _ _ _ Hcount Hcount_units).
    - exact Hskel_units.
    - exact Hsum.
    - exact Hprod_units.
  Qed.

(** The four-path matrix pass remains quadratic without a well-formedness premise. *)
  Lemma increment_pass_clock_le : forall i j d m,
    (M.T_merge
      (increment_row i j d (row_of (M.get j m)) (row_of (M.get (flip i) m))
        (entry m j (flip j)) (entry m (flip i) i))
      (fun x y => T_increment_row i j d
        (row_of (M.get j m)) (row_of (M.get (flip i) m))
        (entry m j (flip j)) (entry m (flip i) i) x y) m M.empty <=
      65536 * (M.c_map + 1) * (M.c_map + 1) *
      N.of_nat ((supp m + 1)^2 *
        (b m + K.bits i + K.bits j + ell m + Z.size_nat d + 1)))%N.
  Proof.
    intros i j d m.
    set (rowwork := increment_row_work i j d
      (row_of (M.get j m)) (row_of (M.get (flip i) m))
      (entry m j (flip j)) (entry m (flip i) i)).
    set (units := (supp m + 1)^2 *
      (b m + K.bits i + K.bits j + ell m + Z.size_nat d + 1)).
    assert (Hpositive : 1 <= units) by (unfold units; cbn [Nat.pow]; nia).
    pose proof (increment_matrix_work_bound m i j d) as Hmatrix.
    assert (Hdata : code_work rowwork m + 1 <= 35 * units).
    { unfold rowwork, units. nia. }
    pose proof (time_of_nat_le _ _ Hdata) as HdataN. rewrite Nat2N.inj_mul in HdataN.
    pose proof (T_merge_left_code_work (M.t Z) (M.t Z) (M.t Z)
      (increment_row i j d (row_of (M.get j m)) (row_of (M.get (flip i) m))
        (entry m j (flip j)) (entry m (flip i) i))
      (fun x y => T_increment_row i j d
        (row_of (M.get j m)) (row_of (M.get (flip i) m))
        (entry m j (flip j)) (entry m (flip i) i) x y)
      rowwork m (512 * (M.c_map + 1))%N
      (T_increment_row_le i j d (row_of (M.get j m)) (row_of (M.get (flip i) m))
        (entry m j (flip j)) (entry m (flip i) i))) as Hmerge.
    eapply N.le_trans; [exact Hmerge|].
    eapply N.le_trans with
      (M.c_map * (512 * (M.c_map + 1) + 1) * 2 * (35 * N.of_nat units))%N.
    - apply N.mul_le_mono_l. exact HdataN.
    - replace (M.c_map * (512 * (M.c_map + 1) + 1) * 2 * (35 * N.of_nat units))%N with
        ((M.c_map * (512 * (M.c_map + 1) + 1) * 2 * 35) * N.of_nat units)%N by ring.
      apply N.mul_le_mono_r. nia.
  Qed.

  (** Zero diagonal seeds add only the four signed endpoint codes. *)
  Lemma increment_seed_bounds : forall i j m,
    let seed := add_cons j j 0%Z (add_cons i i 0%Z m) in
    supp seed <= supp m + 4 /\
    b seed <= b m + K.bits i + K.bits j + 1 /\
    ell seed <= ell m /\
    M.weight seed <= M.weight m + 4 * (K.bits i + K.bits j + 2).
  Proof.
    intros i j m. cbn beta iota zeta.
    set (seed := add_cons j j 0%Z (add_cons i i 0%Z m)).
    assert (Hsupport : forall p, In p (support seed) ->
      p = K.encode i \/ p = K.encode j \/ p = K.encode (flip i) \/
      p = K.encode (flip j) \/ In p (support m)).
    { intros p Hp. unfold seed in Hp. rewrite !support_add_cons in Hp. tauto. }
    destruct (support_signed_endpoints i j seed m Hsupport) as [Hcount Hbits].
    assert (Hmax : Nat.max (b m) (Nat.max (K.bits i) (K.bits j) + 1) <=
      b m + K.bits i + K.bits j + 1).
    { assert (Hij : Nat.max (K.bits i) (K.bits j) <= K.bits i + K.bits j)
        by (apply Nat.max_lub; lia).
      apply Nat.max_lub; lia. }
    split; [exact Hcount|]. split; [lia|]. split.
    - unfold seed. apply ell_add_cons; [|change (0 <= ell m); lia].
      apply ell_add_cons; [lia|change (0 <= ell m); lia].
    - unfold seed.
      pose proof (weight_add_cons j j 0%Z (add_cons i i 0%Z m)).
      pose proof (weight_add_cons i i 0%Z m).
      pose proof (flip_bits i). pose proof (flip_bits j). lia.
  Qed.

  Lemma increment_stage_sizes : forall i j d m,
    let seed := add_cons j j 0%Z (add_cons i i 0%Z m) in
    let next := increment_matrix i j d seed in
    supp next <= supp m + 4 /\
    b next <= b m + K.bits i + K.bits j + 1 /\
    ell next <= ell m + Z.size_nat d + 3 /\
    M.weight next <= M.weight m + 4 * (K.bits i + K.bits j + 2).
  Proof.
    intros i j d m. cbn beta iota zeta.
    set (seed := add_cons j j 0%Z (add_cons i i 0%Z m)).
    destruct (increment_seed_bounds i j m) as [Hcount [Hbits [Hell Hweight]]].
    fold seed in Hcount, Hbits, Hell, Hweight.
    destruct (support_sizes (increment_matrix i j d seed) seed
      (support_increment i j d seed)) as [Hsupport Hkeybits].
    split; [lia|]. split; [lia|]. split.
    - apply ell_increment; lia.
    - eapply Nat.le_trans; [apply weight_increment|exact Hweight].
  Qed.

Lemma tightening_work_le_strengthening : forall m,
    tightening_work m <= strengthening_work m.
  Proof.
    intro m. unfold tightening_work, strengthening_work.
    assert (Hlinear : supp m + 1 <= (supp m + 1)^2) by (cbn [Nat.pow]; nia).
    assert (Hproduct : (supp m + 1) * (b m + ell m + 1) <=
      (supp m + 1)^2 * (b m + ell m + 1)).
    { apply Nat.mul_le_mono_r. exact Hlinear. } lia.
  Qed.

  Lemma diagonal_work_le_strengthening : forall m,
    M.weight m + supp m * (b m + 1) + 1 <= strengthening_work m.
  Proof.
    intro m. unfold strengthening_work.
    assert (Hcount : supp m <= (supp m + 1)^2) by (cbn [Nat.pow]; nia).
    assert (Hproduct : supp m * (b m + 1) <= (supp m + 1)^2 * (b m + ell m + 1)).
    { apply Nat.mul_le_mono; lia. }
    lia.
  Qed.

  (** All post-insertion stages share one raw-label plus quadratic numeric budget. *)
  Lemma increment_stage_work_bound : forall i j d m state,
    supp state <= supp m + 4 ->
    b state <= b m + K.bits i + K.bits j + 1 ->
    ell state <= ell m + Z.size_nat d + 4 ->
    M.weight state <= M.weight m + 4 * (K.bits i + K.bits j + 2) ->
    strengthening_work state <=
      160 * ((supp m + 1)^2 *
        (b m + K.bits i + K.bits j + ell m + Z.size_nat d + 1) + M.weight m).
  Proof.
    intros i j d m state Hcount Hbits Hell Hlabels.
    set (payload := b m + K.bits i + K.bits j + ell m + Z.size_nat d + 1).
    set (units := (supp m + 1)^2 * payload).
    assert (Hpayload : 1 <= payload) by (unfold payload; lia).
    assert (Hunits : payload <= units).
    { unfold units. apply quadratic_payload_le. }
    assert (Hsquare : (supp state + 1)^2 <= 25 * (supp m + 1)^2).
    { cbn [Nat.pow]. nia. }
    assert (Hdata : b state + ell state + 1 <= 6 * payload) by (unfold payload; lia).
    assert (Hproduct : (supp state + 1)^2 * (b state + ell state + 1) <= 150 * units).
    { eapply Nat.le_trans; [apply Nat.mul_le_mono; [exact Hsquare|exact Hdata]|].
      unfold units. nia. }
    assert (Hlabelwork : M.weight state <= M.weight m + 8 * units).
    { unfold payload in Hunits. lia. }
    unfold strengthening_work. fold units. clear Hsquare Hdata Hcount Hbits Hell Hlabels.
    lia.
  Qed.

  (** Incremental closure pays for the seed, four-path pass, and signed integer normalization. *)
  Lemma T_incr_close_le : forall i j d m, (T_incr_close i j d m <=
    c_octagon * N.of_nat (((supp m + 1)^2)%nat) *
      N.of_nat ((b m + K.bits i + K.bits j + ell m + Z.size_nat d + 1)%nat) +
    c_octagon * N.of_nat (M.weight m))%N.
  Proof.
    intros i j d m.
    set (units := (supp m + 1)^2 *
      (b m + K.bits i + K.bits j + ell m + Z.size_nat d + 1)).
    replace (c_octagon * N.of_nat ((supp m + 1)^2) *
      N.of_nat (b m + K.bits i + K.bits j + ell m + Z.size_nat d + 1) +
      c_octagon * N.of_nat (M.weight m))%N with
      (c_octagon * N.of_nat (units + M.weight m))%N
      by (unfold units; rewrite Nat2N.inj_add, Nat2N.inj_mul; ring).
    set (work := N.of_nat (units + M.weight m)).
    set (seed := add_cons j j 0%Z (add_cons i i 0%Z m)).
    set (next := increment_matrix i j d seed).
    set (rounded := tighten next).
    set (finished := strengthen rounded).
    assert (Hkey : K.bits i + K.bits j + Z.size_nat d + 1 <= units).
    { unfold units. eapply Nat.le_trans; [|apply quadratic_payload_le]. lia. }
    assert (Hpositive : (1 <= work)%N) by (unfold work; lia).
    destruct (increment_seed_bounds i j m) as [Hseedn [Hseedb [Hseede Hseedw]]].
    fold seed in Hseedn, Hseedb, Hseede, Hseedw.
    destruct (increment_stage_sizes i j d m) as [Hnextn [Hnextb [Hnexte Hnextw]]].
    fold seed next in Hnextn, Hnextb, Hnexte, Hnextw.
    destruct (support_sizes rounded next (support_tighten next)) as [Hroundn Hroundb].
    pose proof (bits_tighten_le next) as Hrounde.
    pose proof (weight_tighten next) as Hroundw.
    fold rounded in Hrounde, Hroundw.
    destruct (support_sizes finished rounded (support_strengthen rounded)) as [Hfinaln Hfinalb].
    pose proof (bits_strengthen_le rounded) as Hfinale.
    pose proof (weight_strengthen rounded) as Hfinalw.
    fold finished in Hfinale, Hfinalw.
    assert (Hstage : forall state,
      supp state <= supp m + 4 ->
      b state <= b m + K.bits i + K.bits j + 1 ->
      ell state <= ell m + Z.size_nat d + 4 ->
      M.weight state <= M.weight m + 4 * (K.bits i + K.bits j + 2) ->
      (N.of_nat (strengthening_work state) <= 160 * work)%N).
    { intros state Hn Hb He Hw.
      pose proof (increment_stage_work_bound i j d m state Hn Hb He Hw) as Hbound.
      fold units in Hbound. pose proof (time_of_nat_le _ _ Hbound) as Hcast.
      rewrite Nat2N.inj_mul in Hcast. exact Hcast. }
    assert (Hnextwork : (N.of_nat (strengthening_work next) <= 160 * work)%N).
    { apply Hstage; lia. }
    assert (Hroundwork : (N.of_nat (strengthening_work rounded) <= 160 * work)%N).
    { apply Hstage; lia. }
    assert (Hfinalwork : (N.of_nat (strengthening_work finished) <= 160 * work)%N).
    { apply Hstage; lia. }
    assert (Hpassdata : (supp seed + 1)^2 *
      (b seed + K.bits i + K.bits j + ell seed + Z.size_nat d + 1) <=
      50 * (units + M.weight m)).
    { assert (Hsquare : (supp seed + 1)^2 <= 25 * (supp m + 1)^2).
      { clear -Hseedn. cbn [Nat.pow]. nia. }
      assert (Hpayload : b seed + K.bits i + K.bits j + ell seed + Z.size_nat d + 1 <=
        2 * (b m + K.bits i + K.bits j + ell m + Z.size_nat d + 1)).
      { clear -Hseedb Hseede. lia. }
      eapply Nat.le_trans; [apply Nat.mul_le_mono; [exact Hsquare|exact Hpayload]|].
      replace ((25 * (supp m + 1)^2) *
        (2 * (b m + K.bits i + K.bits j + ell m + Z.size_nat d + 1))) with
        (50 * units) by (unfold units; ring).
      apply Nat.mul_le_mono_l. clear -units m. clearbody units. lia. }
    assert (Hpass : (M.T_merge
      (increment_row i j d (row_of (M.get j seed)) (row_of (M.get (flip i) seed))
        (entry seed j (flip j)) (entry seed (flip i) i))
      (fun x y => T_increment_row i j d
        (row_of (M.get j seed)) (row_of (M.get (flip i) seed))
        (entry seed j (flip j)) (entry seed (flip i) i) x y) seed M.empty <=
      3276800 * (M.c_map + 1) * (M.c_map + 1) * work)%N).
    { eapply N.le_trans; [apply increment_pass_clock_le|].
      replace (3276800 * (M.c_map + 1) * (M.c_map + 1) * work)%N with
        (65536 * (M.c_map + 1) * (M.c_map + 1) * (50 * work))%N by ring.
      apply N.mul_le_mono_l.
      pose proof (time_of_nat_le _ _ Hpassdata) as Hcast.
      now rewrite (Nat2N.inj_mul 50 (units + M.weight m)) in Hcast. }
    assert (Htighten : (T_tighten next <=
      40960 * (M.c_map + 1) * (M.c_map + 1) * work)%N).
    { eapply N.le_trans; [apply T_tighten_small|].
      replace (40960 * (M.c_map + 1) * (M.c_map + 1) * work)%N with
        (256 * (M.c_map + 1) * (M.c_map + 1) * (160 * work))%N by ring.
      apply N.mul_le_mono_l. eapply N.le_trans; [|exact Hnextwork].
      apply time_of_nat_le, tightening_work_le_strengthening. }
    assert (Hstrengthen : (T_strengthen rounded <=
      655360 * (M.c_map + 1) * (M.c_map + 1) * work)%N).
    { eapply N.le_trans; [apply T_strengthen_small|].
      replace (655360 * (M.c_map + 1) * (M.c_map + 1) * work)%N with
        (4096 * (M.c_map + 1) * (M.c_map + 1) * (160 * work))%N by ring.
      apply N.mul_le_mono_l. exact Hroundwork. }
    assert (Hscan : forall state, (N.of_nat (strengthening_work state) <= 160 * work)%N ->
      (T_matrix_ok state <= 20480 * (M.c_map + 1) * (M.c_map + 1) * work)%N).
    { intros state Hbound. eapply N.le_trans; [apply T_matrix_ok_small|].
      replace (20480 * (M.c_map + 1) * (M.c_map + 1) * work)%N with
        (128 * (M.c_map + 1) * (M.c_map + 1) * (160 * work))%N by ring.
      apply N.mul_le_mono_l. eapply N.le_trans; [|exact Hbound].
      apply time_of_nat_le, diagonal_work_le_strengthening. }
    pose proof (Hscan next Hnextwork) as Hscan1.
    pose proof (Hscan finished Hfinalwork) as Hscan2.
    assert (Hinsert : forall x state, K.bits x <= K.bits i + K.bits j ->
      (T_add_cons x x 0%Z state <= 512 * (M.c_map + 1) * work)%N).
    { intros x state Hbits. eapply N.le_trans; [apply T_add_cons_small|].
      replace (512 * (M.c_map + 1) * work)%N with
        (256 * (M.c_map + 1) * (2 * work))%N by ring.
      apply N.mul_le_mono_l.
      assert (Hbound : K.bits x + K.bits x + Z.size_nat 0%Z + 1 <=
        2 * (units + M.weight m)) by (cbn [Z.size_nat]; lia).
      pose proof (time_of_nat_le _ _ Hbound) as Hcast.
      now rewrite Nat2N.inj_mul in Hcast. }
    pose proof (Hinsert i m ltac:(lia)) as Hinsert1.
    pose proof (Hinsert j (add_cons i i 0%Z m) ltac:(lia)) as Hinsert2.
    assert (Hlookup : forall k (state : dbm), K.bits k + 1 <= 2 * (units + M.weight m) ->
      (M.T_get k state <= 2 * M.c_map * work)%N).
    { intros k state Hbound. eapply N.le_trans; [apply M.T_get_le|].
      replace (2 * M.c_map * work)%N with (M.c_map * (2 * work))%N by ring.
      apply N.mul_le_mono_l. pose proof (time_of_nat_le _ _ Hbound) as Hcast.
      now rewrite Nat2N.inj_mul in Hcast. }
    pose proof (flip_bits i) as Hflipi. pose proof (flip_bits j) as Hflipj.
    pose proof (Hlookup j seed ltac:(lia)) as Hget1.
    pose proof (Hlookup (flip i) seed ltac:(lia)) as Hget2.
    assert (Hentry : forall a b,
      K.bits a + K.bits b + 1 <= 2 * (units + M.weight m) ->
      (T_entry seed a b <= 16 * (M.c_map + 1) * work)%N).
    { intros a b Hbound. eapply N.le_trans; [apply T_entry_small|].
      replace (16 * (M.c_map + 1) * work)%N with
        (8 * (M.c_map + 1) * (2 * work))%N by ring.
      apply N.mul_le_mono_l. pose proof (time_of_nat_le _ _ Hbound) as Hcast.
      now rewrite Nat2N.inj_mul in Hcast. }
    pose proof (Hentry j (flip j) ltac:(lia)) as Hentry1.
    pose proof (Hentry (flip i) i ltac:(lia)) as Hentry2.
    pose proof (T_row_of_le (M.get j seed)) as Hrow1.
    pose proof (T_row_of_le (M.get (flip i) seed)) as Hrow2.
    pose proof (T_flip_le i) as Hflip1. pose proof (T_flip_le j) as Hflip2.
    assert (Hcoefficient : (4014080 * (M.c_map + 1) * (M.c_map + 1) +
      2048 * (M.c_map + 1) + 64 <= c_octagon)%N).
    { pose proof (N.le_0_l M.c_map) as Hmap. clear -Hmap. unfold c_octagon. nia. }
    pose proof (N.mul_le_mono_r _ _ work Hcoefficient) as Hbudget.
    repeat rewrite N.mul_add_distr_r in Hbudget.
    clear Hkey Hseedn Hseedb Hseede Hseedw Hnextn Hnextb Hnexte Hnextw
      Hroundn Hroundb Hrounde Hroundw Hfinaln Hfinalb Hfinale Hfinalw
      Hstage Hnextwork Hroundwork Hfinalwork Hpassdata Hscan Hinsert Hlookup
      Hentry Hflipi Hflipj Hcoefficient.
    clearbody work. clear units. unfold T_incr_close. cbn beta iota zeta.
    fold seed. fold increment_matrix. fold next rounded finished.
    match goal with
    | |- context [M.T_merge ?step ?callback seed M.empty] =>
      assert (Hpass_actual : (M.T_merge step callback seed M.empty <=
        3276800 * (M.c_map + 1) * (M.c_map + 1) * work)%N) by exact Hpass;
      set (pass_cost := M.T_merge step callback seed M.empty) in *
    end.
    clearbody pass_cost.
    change (1 +
      (T_add_cons i i 0%Z m + T_add_cons j j 0%Z (add_cons i i 0%Z m) +
       (M.T_get j seed + T_row_of (M.get j seed) +
        (T_flip i + M.T_get (flip i) seed + T_row_of (M.get (flip i) seed) +
         (T_flip j + T_entry seed j (flip j) +
          (T_flip i + T_entry seed (flip i) i))) + pass_cost +
        (T_matrix_ok next +
         (if matrix_ok next then
            T_tighten next + T_strengthen rounded + T_matrix_ok finished
          else 0)))) <= c_octagon * work)%N.
    clearbody seed next rounded finished.
    destruct (matrix_ok next); cbn beta iota zeta; lia.
  Qed.

  Definition range_payload (e : term L.op X.t) (m : dbm) : nat :=
    b m + ell m + F.bits_e e + Nat.log2 (tsize e) + 1.

  (** The interval arithmetic charge is the square of its combined bit allowance. *)
  Definition range_unit (e : term L.op X.t) (m : dbm) : N :=
    N.of_nat ((range_payload e m ^ 2)%nat).

  (** Every range arithmetic allowance contains one unit for fixed work. *)
  Lemma range_payload_positive : forall e m, 1 <= range_payload e m.
  Proof.
    intros e m. unfold range_payload. lia.
  Qed.

  (** A positive squared allowance also pays for linear arithmetic. *)
  Lemma range_unit_linear : forall e m,
    (N.of_nat (range_payload e m) <= range_unit e m)%N.
  Proof.
    intros e m. unfold range_unit. apply time_of_nat_le.
    pose proof (range_payload_positive e m) as Hpositive.
    cbn [Nat.pow]. rewrite Nat.mul_1_r.
    replace (range_payload e m) with (range_payload e m * 1) at 1 by lia.
    apply Nat.mul_le_mono; [apply Nat.le_refl|exact Hpositive].
  Qed.

  (** The arithmetic charge is nonzero on every source term and state. *)
  Lemma range_unit_positive : forall e m, (1 <= range_unit e m)%N.
  Proof.
    intros e m. eapply N.le_trans; [|apply range_unit_linear].
    change (N.of_nat 1%nat <= N.of_nat (range_payload e m))%N.
    apply time_of_nat_le. apply range_payload_positive.
  Qed.

  (** Every mentioned key fits the maximum charged by its linear form. *)
  Lemma form_bits_key : forall f p,
    In p (coef f) -> X.bits (fst p) <= F.form_bits f.
  Proof.
    intros [cs c] p. unfold F.form_bits. cbn [coef cst].
    induction cs as [|q cs IH]; intros Hin; [contradiction|].
    cbn in Hin |- *. destruct Hin as [Heq|Hin].
    - subst q. pose proof (Nat.le_max_l
        (X.bits (fst p) + Z.size_nat (snd p))
        (fold_right Nat.max (Z.size_nat c)
          (map (fun p => X.bits (fst p) + Z.size_nat (snd p)) cs))). lia.
    - eapply Nat.le_trans; [now apply IH|apply Nat.le_max_r].
  Qed.

  (** A source form's suffix accumulators retain the same logarithmic bit allowance. *)
  Lemma form_fragment_abs : forall e m f r cs,
    F.lin_of e = Some (f, r) -> incl cs (coef f) -> length cs <= tsize e ->
    rel_bounds_abs (2 ^ range_bits e (Reached m))
      (rel_form_bounds (variable_bounds m) (Lin X.t cs (cst f))).
  Proof.
    intros e m f r cs Hlin Hincl Hcount.
    destruct (F.lin_of_size e f r Hlin) as [_ Hbits].
    eapply rel_bounds_abs_mono with
      (lower := (length cs + 1) * 2 ^ F.bits_e e * 2 ^ ell m).
    - unfold range_bits, ells. apply affine_magnitude_allowance; [exact Hcount|].
      destruct e; cbn [tsize]; lia.
    - apply rel_form_bounds_abs.
      + cbn [cst]. apply zbits_abs_bound.
        eapply Nat.le_trans; [exact (form_bits_constant f)|]. lia.
      + cbn [coef]. apply Forall_forall. intros p Hin. apply zbits_abs_bound.
        eapply Nat.le_trans; [exact (form_bits_coefficient f p (Hincl p Hin))|]. lia.
      + apply variable_bounds_abs.
      + pose proof (Nat.pow_nonzero 2 (F.bits_e e) ltac:(lia)). lia.
      + pose proof (Nat.pow_nonzero 2 (ell m) ltac:(lia)). lia.
  Qed.

(** Signed unary queries charge halving as well as the two encoded-key lookups. *)
  Lemma T_variable_bounds_small : forall m x,
    (T_variable_bounds m x <=
      128 * (M.c_map + 1) * N.of_nat (X.bits x + ell m + 1))%N.
  Proof.
    intros m x.
    pose proof (T_entry_small m (x, true) (x, false)) as Hlower.
    pose proof (T_entry_small m (x, false) (x, true)) as Hupper.
    rewrite !literal_bits in Hlower, Hupper.
    cbn beta iota zeta in Hlower, Hupper.
    assert (Hhalf : forall a b z, entry m a b = Some z ->
      (Z.T_div2 z <= N.of_nat (ell m) + 2)%N).
    { intros a b z Hz. eapply N.le_trans; [apply Z.T_div2_le|].
      assert (Hbits : Z.size_nat z <= ell m).
      { apply (ell_entry m (K.encode a) (K.encode b) z). now rewrite raw_entry_get. }
      apply N.add_le_mono_r. now apply time_of_nat_le. }
    set (key_bits := X.bits x) in *.
    set (entry_bits := ell m) in *.
    clearbody key_bits entry_bits.
    unfold T_variable_bounds. time_simpl.
    destruct (entry m (x, true) (x, false)) as [lo|] eqn:Hlo;
      destruct (entry m (x, false) (x, true)) as [hi|] eqn:Hhi;
      try pose proof (Hhalf _ _ _ Hlo) as Hhalflo;
      try pose proof (Hhalf _ _ _ Hhi) as Hhalfhi;
      time_simpl; time_cbn;
      try match goal with |- context [Z.T_opp ?z] => pose proof (Z.T_opp_le z) end;
      rewrite ?Nat2N.inj_add, ?Nat2N.inj_mul in *; nia.
  Qed.

  (** A smaller linear allowance fits the shared squared range charge. *)
  Lemma range_linear_charge : forall e m bits,
    bits <= range_payload e m -> (N.of_nat bits <= range_unit e m)%N.
  Proof.
    intros e m bits Hbits. eapply N.le_trans; [|apply range_unit_linear].
    now apply time_of_nat_le.
  Qed.

  (** Squaring a smaller bit allowance preserves the range budget. *)
  Lemma range_square_charge : forall e m bits,
    bits <= range_payload e m -> (N.of_nat (bits ^ 2) <= range_unit e m)%N.
  Proof.
    intros e m bits Hbits. unfold range_unit. apply time_of_nat_le.
    cbn [Nat.pow]. rewrite !Nat.mul_1_r. now apply Nat.mul_le_mono.
  Qed.

  (** A coefficient key lookup fits one range arithmetic charge. *)
  Lemma T_variable_bounds_range : forall e m x,
    X.bits x <= F.bits_e e ->
    (T_variable_bounds m x <= 128 * (M.c_map + 1) * range_unit e m)%N.
  Proof.
    intros e m x Hbits. eapply N.le_trans; [apply T_variable_bounds_small|].
    apply N.mul_le_mono_l. apply range_linear_charge. unfold range_payload. lia.
  Qed.

  (** Coefficient multiplication uses the source and matrix endpoint bit allowances. *)
  Lemma T_scale_bounds_range : forall e m c x,
    Z.size_nat c <= F.bits_e e ->
    (T_rel_scale_bounds c (variable_bounds m x) <= 32 * range_unit e m)%N.
  Proof.
    intros e m c x Hbits.
    eapply N.le_trans.
    - apply rel_scale_bounds_time with (bits_c := F.bits_e e) (bits_x := ell m).
      + exact Hbits.
      + apply variable_bounds_abs.
    - apply N.mul_le_mono_l. apply range_square_charge. unfold range_payload. lia.
  Qed.

  (** Adding a product to a source suffix costs a linear fraction of the squared budget. *)
  Lemma T_add_bounds_range : forall e m a acc,
    rel_bounds_abs (2 ^ (F.bits_e e + ell m)) a ->
    rel_bounds_abs (2 ^ range_bits e (Reached m)) acc ->
    (T_rel_add_bounds a acc <= 48 * range_unit e m)%N.
  Proof.
    intros e m a acc Ha Hacc.
    eapply N.le_trans; [exact (rel_add_bounds_time _ _ _ _ Ha Hacc)|].
    replace (48 * range_unit e m)%N with (16 * (3 * range_unit e m))%N by ring.
    apply N.mul_le_mono_l.
    eapply N.le_trans with (N.of_nat (3 * range_payload e m)).
    - apply time_of_nat_le. unfold range_bits, ells, range_payload. lia.
    - rewrite Nat2N.inj_mul. change (3 * N.of_nat (range_payload e m) <=
        3 * range_unit e m)%N.
      apply N.mul_le_mono_l. apply range_unit_linear.
  Qed.

  (** Source wrap endpoints are already part of the charged linearization bits. *)
  Lemma T_wrap_bounds_range : forall e m f r bounds,
    F.lin_of e = Some (f, r) ->
    (T_rel_wrap_bounds r bounds <= 8 * range_unit e m)%N.
  Proof.
    intros e m f r bounds Hlin.
    destruct (F.lin_of_size e f r Hlin) as [_ Hbits].
    eapply N.le_trans.
    - apply rel_wrap_bounds_time with (bits := F.bits_e e).
      change (F.wrap_bits r <= F.bits_e e). lia.
    - apply N.mul_le_mono_l. apply range_linear_charge. unfold range_payload. lia.
  Qed.

  (** Each actual form-fold step has bounded queries, products and suffix addition. *)
  Lemma form_bounds_step_time : forall e m f r p after,
    F.lin_of e = Some (f, r) -> In p (coef f) -> incl after (coef f) ->
    length after <= tsize e ->
    (16 + T_variable_bounds m (fst p) +
      T_rel_scale_bounds (snd p) (variable_bounds m (fst p)) +
      T_rel_add_bounds (rel_scale_bounds (snd p) (variable_bounds m (fst p)))
        (rel_form_bounds (variable_bounds m) (Lin X.t after (cst f))) <=
      512 * (M.c_map + 1) * range_unit e m)%N.
  Proof.
    intros e m f r p after Hlin Hin Hincl Hcount.
    destruct (F.lin_of_size e f r Hlin) as [_ Hbits].
    assert (Hkey : X.bits (fst p) <= F.bits_e e).
    { pose proof (form_bits_key f p Hin). lia. }
    assert (Hcoefficient : Z.size_nat (snd p) <= F.bits_e e).
    { pose proof (form_bits_coefficient f p Hin). lia. }
    assert (Hproduct : rel_bounds_abs (2 ^ (F.bits_e e + ell m))
      (rel_scale_bounds (snd p) (variable_bounds m (fst p)))).
    { rewrite Nat.pow_add_r. apply rel_bounds_abs_scale.
      - now apply zbits_abs_bound.
      - apply variable_bounds_abs.
      - pose proof (Nat.pow_nonzero 2 (F.bits_e e) ltac:(lia)). lia.
      - pose proof (Nat.pow_nonzero 2 (ell m) ltac:(lia)). lia. }
    pose proof (form_fragment_abs e m f r after Hlin Hincl Hcount) as Hsuffix.
    pose proof (T_variable_bounds_range e m (fst p) Hkey) as Hquery.
    pose proof (T_scale_bounds_range e m (snd p) (fst p) Hcoefficient) as Hscale.
    pose proof (T_add_bounds_range e m _ _ Hproduct Hsuffix) as Hadd.
    assert (Hcharge : (range_unit e m <= (M.c_map + 1) * range_unit e m)%N).
    { replace (range_unit e m) with (1 * range_unit e m)%N at 1 by ring.
      apply N.mul_le_mono_r. lia. }
    pose proof (N.mul_le_mono_l _ _ 32%N Hcharge) as Hscale_charge.
    pose proof (N.mul_le_mono_l _ _ 48%N Hcharge) as Hadd_charge.
    pose proof (range_unit_positive e m) as Hpositive.
    replace (128 * (M.c_map + 1) * range_unit e m)%N with
      (128 * ((M.c_map + 1) * range_unit e m))%N in Hquery by ring.
    replace (512 * (M.c_map + 1) * range_unit e m)%N with
      (512 * ((M.c_map + 1) * range_unit e m))%N by ring.
    set (charge := ((M.c_map + 1) * range_unit e m)%N) in *.
    clear Hbits Hkey Hcoefficient Hproduct Hsuffix. clearbody charge. lia.
  Qed.

  (** Summing bounded steps and the fold frame adds one source-size factor. *)
  Lemma range_fold_budget : forall fold_cost count nodes unit : N,
    (1 <= unit)%N -> (count <= nodes)%N ->
    (fold_cost <= (512 * unit + 1) * count + 1)%N ->
    (8 + fold_cost <= 1024 * unit * (nodes + 1))%N.
  Proof.
    intros fold_cost count nodes unit Hunit Hcount Hfold.
    assert (Hcount_unit : (count <= unit * count)%N).
    { replace count with (1 * count)%N at 1 by ring.
      apply N.mul_le_mono_r. exact Hunit. }
    assert (Hproduct : (unit * count <= unit * nodes)%N).
    { now apply N.mul_le_mono_l. }
    replace ((512 * unit + 1) * count + 1)%N with
      (512 * (unit * count) + count + 1)%N in Hfold by ring.
    replace (1024 * unit * (nodes + 1))%N with
      (1024 * (unit * nodes) + 1024 * unit)%N by ring.
    set (count_charge := (unit * count)%N) in *.
    set (node_charge := (unit * nodes)%N) in *.
    clearbody count_charge node_charge. lia.
  Qed.

  (** The actual affine fold is linear in source size at the squared bit charge. *)
  Lemma T_form_bounds_source : forall e m f r,
    F.lin_of e = Some (f, r) ->
    (T_form_bounds m f <= 1024 * (M.c_map + 1) *
      (N.of_nat ((tsize e + 1)%nat) * range_unit e m))%N.
  Proof.
    intros e m [cs c] r Hlin.
    destruct (F.lin_of_size e (Lin X.t cs c) r Hlin) as [Hcount Hbits].
    cbn [coef] in Hcount.
    time_unfold (@T_form_bounds). time_simpl. time_cbn.
    time_unfold (@T_rel_form_bounds). time_simpl. time_cbn.
    lazymatch goal with
    | |- context [Std.List.T_fold_right ?ff ?tf ?seed ?xs] =>
      assert (Hfold : (Std.List.T_fold_right ff tf seed xs <=
        (512 * ((M.c_map + 1) * range_unit e m) + 1) *
          N.of_nat (length xs) + 1)%N)
    end.
    { apply rel_fold_right_time. intros before p after Heq.
      assert (Hin : In p (coef (Lin X.t cs c))).
      { cbn [coef]. rewrite Heq. apply in_or_app. right. now left. }
      assert (Hincl : incl after (coef (Lin X.t cs c))).
      { intros q Hq. cbn [coef]. rewrite Heq. apply in_or_app. right. now right. }
      assert (Hafter : length after <= tsize e).
      { rewrite Heq, length_app in Hcount. cbn [length] in Hcount. lia. }
      pose proof (form_bounds_step_time e m (Lin X.t cs c) r p after
        Hlin Hin Hincl Hafter) as Hstep.
      unfold rel_form_bounds in Hstep. cbn [coef cst] in Hstep.
      replace (512 * (M.c_map + 1) * range_unit e m)%N with
        (512 * ((M.c_map + 1) * range_unit e m))%N in Hstep by ring.
      eapply N.le_trans; [|exact Hstep]. time_simpl. time_cbn. lia. }
    assert (Hunit : (1 <= (M.c_map + 1) * range_unit e m)%N).
    { eapply N.le_trans; [apply range_unit_positive|].
      replace (range_unit e m) with (1 * range_unit e m)%N at 1 by ring.
      apply N.mul_le_mono_r. lia. }
    pose proof (time_of_nat_le _ _ Hcount) as HcountN.
    pose proof (range_fold_budget _ _ _ _ Hunit HcountN Hfold) as Htotal.
    rewrite Nat2N.inj_add. change (N.of_nat 1%nat) with 1%N.
    replace (1024 * (M.c_map + 1) *
      ((N.of_nat (tsize e) + 1) * range_unit e m))%N with
      (1024 * ((M.c_map + 1) * range_unit e m) * (N.of_nat (tsize e) + 1))%N
      by ring.
    eapply N.le_trans; [|exact Htotal]. lia.
  Qed.

  (** The public numeric coefficient pays the affine range fold with fixed slack. *)
  Lemma c_num_range_coefficient : (4096 * (M.c_map + 1) <= c_num)%N.
  Proof.
    unfold c_num. nia.
  Qed.

  (** Actual linearization time is charged additively beside the interval fold. *)
  Lemma range_public_budget : forall form_cost wrap_cost lin_cost work : N,
    (form_cost <= 1024 * (M.c_map + 1) * work)%N ->
    (wrap_cost <= 8 * work)%N ->
    (8 + lin_cost + form_cost + wrap_cost <= c_num * (work + lin_cost + 1))%N.
  Proof.
    intros form_cost wrap_cost lin_cost work Hform Hwrap.
    pose proof c_num_range_coefficient as Hcoefficient.
    assert (Hcombined : (1024 * (M.c_map + 1) + 8 <= c_num)%N) by lia.
    pose proof (N.mul_le_mono_r _ _ work Hcombined) as Hwork.
    rewrite N.mul_add_distr_r in Hwork.
    assert (Hlinear : (lin_cost <= c_num * lin_cost)%N).
    { replace lin_cost with (1 * lin_cost)%N at 1 by ring.
      apply N.mul_le_mono_r. lia. }
    replace (c_num * (work + lin_cost + 1))%N with
      (c_num * work + c_num * lin_cost + c_num)%N by ring.
    lia.
  Qed.

  (** Range queries charge every performed form step and the actual linearizer clock. *)
  Lemma T_range_le : forall e s,
    (T_range e s <= c_num * N.of_nat (range_work e s + 1))%N.
  Proof.
    intros e [|m].
    - assert (Hpositive : (1 <= c_num)%N).
      { pose proof c_num_range_coefficient. lia. }
      assert (Hwork : (1 <= N.of_nat (range_work e Unreached + 1))%N).
      { change (N.of_nat 1%nat <= N.of_nat (range_work e Unreached + 1))%N.
        apply time_of_nat_le. lia. }
      pose proof (N.mul_le_mono _ _ _ _ Hpositive Hwork) as Hbudget.
      time_unfold (@T_range). time_simpl. time_cbn. lia.
    - set (work := (N.of_nat ((tsize e + 1)%nat) * range_unit e m)%N).
      assert (Hwork : N.of_nat (range_work e (Reached m) + 1) =
        (work + F.T_lin_of e + 1)%N).
      { rewrite Nat2N.inj_add, F_range_work. cbn [bs ells].
        unfold work, range_unit, range_payload. rewrite Nat2N.inj_mul.
        reflexivity. }
      assert (Hunit_work : (range_unit e m <= work)%N).
      { unfold work. replace (range_unit e m) with (1 * range_unit e m)%N at 1 by ring.
        apply N.mul_le_mono_r.
        change (N.of_nat 1%nat <= N.of_nat (tsize e + 1))%N.
        apply time_of_nat_le. lia. }
      rewrite Hwork. time_unfold (@T_range).
      destruct (F.lin_of e) as [[f r]|] eqn:Hlin.
      + pose proof (T_form_bounds_source e m f r Hlin) as Hform.
        change (T_form_bounds m f <= 1024 * (M.c_map + 1) * work)%N in Hform.
        pose proof (T_wrap_bounds_range e m f r (form_bounds m f) Hlin) as Hwrap.
        assert (Hwrap_work : (T_rel_wrap_bounds r (form_bounds m f) <= 8 * work)%N).
        { eapply N.le_trans; [exact Hwrap|]. now apply N.mul_le_mono_l. }
        pose proof (range_public_budget _ _ (F.T_lin_of e) work Hform Hwrap_work) as Htotal.
        eapply N.le_trans; [|exact Htotal]. time_simpl. time_cbn. lia.
      + pose proof (range_public_budget 0 0 (F.T_lin_of e) work
          ltac:(lia) ltac:(lia)) as Htotal.
        eapply N.le_trans; [|exact Htotal]. time_simpl. time_cbn. lia.
  Qed.

  (** Signed havoc removes both literal rows and columns without changing retained entries. *)
  Lemma raw_entry_havoc : forall x m p q,
    raw_entry (M.merge (forget_row x)
      (M.remove (x, true) (M.remove (x, false) m)) M.empty) p q =
    if Pos.eqb p (K.encode (x, true)) then None else
      if Pos.eqb p (K.encode (x, false)) then None else
        if Pos.eqb q (K.encode (x, true)) then None else
          if Pos.eqb q (K.encode (x, false)) then None else raw_entry m p q.
  Proof.
    intros x m p q. unfold raw_entry.
    rewrite M.find_merge by reflexivity. rewrite M.find_empty, !M.find_remove.
    destruct (Pos.eqb p (K.encode (x, true))).
    - cbn [forget_row row_of]. apply M.find_empty.
    - destruct (Pos.eqb p (K.encode (x, false))).
      + cbn [forget_row row_of]. apply M.find_empty.
      + destruct (M.find p m) as [row|]; cbn [forget_row row_of].
        * now rewrite !M.find_remove.
        * rewrite M.find_empty. destruct (Pos.eqb q (K.encode (x, true)));
            destruct (Pos.eqb q (K.encode (x, false))); reflexivity.
  Qed.

  (** Forgetting both literals introduces no raw support code, regardless of labels. *)
  Lemma support_havoc : forall x m p,
    In p (support (M.merge (forget_row x)
      (M.remove (x, true) (M.remove (x, false) m)) M.empty)) ->
    In p (support m).
  Proof.
    intros x m p Hin. apply support_find in Hin. apply support_find.
    destruct Hin as [Hrow|[q Hentry]].
    - rewrite M.find_merge in Hrow by reflexivity.
      rewrite M.find_empty, !M.find_remove in Hrow.
      destruct (Pos.eqb p (K.encode (x, true))); cbn [forget_row] in Hrow;
        [contradiction|].
      destruct (Pos.eqb p (K.encode (x, false))); cbn [forget_row] in Hrow;
        [contradiction|].
      destruct (M.find p m) as [row|] eqn:Hp; cbn [forget_row] in Hrow.
      + left. discriminate.
      + contradiction.
    - rewrite raw_entry_havoc in Hentry.
      destruct (Pos.eqb q (K.encode (x, true))); [contradiction|].
      destruct (Pos.eqb q (K.encode (x, false))); [contradiction|].
      destruct (Pos.eqb p (K.encode (x, true))); [contradiction|].
      destruct (Pos.eqb p (K.encode (x, false))); [contradiction|].
      right. now exists q.
  Qed.

  (** Signed havoc decreases support, entry bits, key bits, and the stored-label allowance. *)
  Lemma havoc_resources : forall x s,
    ns (havoc x s) <= ns s /\ bs (havoc x s) <= bs s /\
      ells (havoc x s) <= ells s /\ labs (havoc x s) <= labs s.
  Proof.
    intros x [|m].
    - cbn [havoc ns bs ells labs]. repeat split; lia.
    - cbn [havoc ns bs ells labs]. split.
      + unfold supp. apply NoDup_incl_length; [apply support_nodup|].
        intros p Hp. now apply (support_havoc x m p).
      + split.
        * unfold b at 1. apply maximum_bound. intros p Hp.
          apply support_bits. now apply (support_havoc x m p).
        * split.
          -- apply ell_bound. intros p q z Hz. rewrite raw_entry_havoc in Hz.
             destruct (Pos.eqb p (K.encode (x, true))); [discriminate|].
             destruct (Pos.eqb p (K.encode (x, false))); [discriminate|].
             destruct (Pos.eqb q (K.encode (x, true))); [discriminate|].
             destruct (Pos.eqb q (K.encode (x, false))); [discriminate|].
             now apply (ell_entry m p q z).
          -- eapply Nat.le_trans; [apply M.weight_merge_l; intros; reflexivity|].
             eapply Nat.le_trans; [apply M.weight_remove|apply M.weight_remove].
  Qed.

  Lemma support_nat_codes_nodup : forall ps,
    NoDup ps -> NoDup (map Pos.to_nat ps).
  Proof.
    intros ps Hdistinct. induction Hdistinct as [|p ps Hfresh Hdistinct IH].
    - constructor.
    - cbn. constructor; [|exact IH]. intro Hin. apply in_map_iff in Hin.
      destruct Hin as [q [Heq Hq]]. apply Pos2Nat.inj in Heq. subst q.
      exact (Hfresh Hq).
  Qed.

  (** Distinct positive codes of at most b bits occupy at most the nonzero b-bit integers. *)
  Lemma support_cardinality_power : forall m, supp m + 1 <= 2 ^ b m.
  Proof.
    intro m.
    assert (Hpositive : 1 <= 2 ^ b m).
    { change (2 ^ 0 <= 2 ^ b m). apply Nat.pow_le_mono_r; lia. }
    assert (Hlength : length (map Pos.to_nat (support m)) <= length (seq 1 (2 ^ b m - 1))).
    { apply NoDup_incl_length.
      - apply support_nat_codes_nodup, support_nodup.
      - intros n Hin. apply in_map_iff in Hin. destruct Hin as [p [Heq Hp]]. subst n.
        apply in_seq. pose proof (Pos2Nat.is_pos p) as Hnonzero.
        assert (Hupper : Pos.to_nat p < 2 ^ b m).
        { eapply Nat.lt_le_trans; [apply Pos.size_nat_upper|].
          apply Nat.pow_le_mono_r; [lia|now apply support_bits]. }
        split; lia. }
    rewrite length_map, length_seq in Hlength. unfold supp. lia.
  Qed.

  (** The support count's logarithm is already covered by the encoded-key bit allowance. *)
  Lemma log2_support_le : forall m, Nat.log2 (supp m + 1) <= b m.
  Proof.
    intro m. pose proof (Nat.log2_le_mono _ _ (support_cardinality_power m)) as Hlog.
    rewrite Nat.log2_pow2 in Hlog by lia. exact Hlog.
  Qed.

  (** Mapping a finite optional payload preserves whether the binding exists. *)
  Lemma shift_option_presence : forall A B (f : A -> B) a,
    option_map f a <> None <-> a <> None.
  Proof.
    intros A B f [a|]; cbn; split; congruence.
  Qed.

  (** Equal outer and entry presence gives equal raw support membership. *)
  Lemma support_by_presence : forall ma mb,
    (forall p, M.find p ma <> None <-> M.find p mb <> None) ->
    (forall p q, raw_entry ma p q <> None <-> raw_entry mb p q <> None) ->
    forall p, In p (support ma) <-> In p (support mb).
  Proof.
    intros ma mb Houter Hentry p. rewrite !support_find. split.
    - intros [Hrow|[q Hraw]].
      + left. now apply Houter.
      + right. exists q. now apply Hentry.
    - intros [Hrow|[q Hraw]].
      + left. now apply Houter.
      + right. exists q. now apply Hentry.
  Qed.

  (** Updating the selected column changes a payload only where that code already exists. *)
  Lemma find_shift_column_row : forall (target : K.t) d row q,
    M.find q (row_of (shift_column_row target d (Some row) None)) =
      option_map (fun z => if Pos.eqb q (K.encode target) then (z + d)%Z else z)
        (M.find q row).
  Proof.
    intros target d row q. unfold shift_column_row. cbn [row_of].
    rewrite M.get_find.
    destruct (M.find (K.encode target) row) as [old|] eqn:Hselected.
    - rewrite M.find_set. destruct (Pos.eqb q (K.encode target)) eqn:Hsame.
      + apply Pos.eqb_eq in Hsame. subst q. now rewrite Hselected.
      + destruct (M.find q row); reflexivity.
    - destruct (Pos.eqb q (K.encode target)) eqn:Hsame.
      + apply Pos.eqb_eq in Hsame. subst q. now rewrite Hselected.
      + destruct (M.find q row); reflexivity.
  Qed.

  (** A column shift_literal retains exactly the existing outer row bindings. *)
  Lemma find_shift_columns_presence : forall (target : K.t) d m p,
    M.find p (shift_columns target d m) <> None <-> M.find p m <> None.
  Proof.
    intros target d m p. unfold shift_columns.
    rewrite M.find_merge by reflexivity. rewrite M.find_empty.
    destruct (M.find p m) as [row|]; cbn [shift_column_row].
    - split; intros _ H; discriminate H.
    - tauto.
  Qed.

  (** Raw column-shift_literal lookup is independent of stored labels. *)
  Lemma raw_entry_shift_columns : forall (target : K.t) d m p q,
    raw_entry (shift_columns target d m) p q =
      option_map (fun z => if Pos.eqb q (K.encode target) then (z + d)%Z else z)
        (raw_entry m p q).
  Proof.
    intros target d m p q. unfold raw_entry, shift_columns.
    rewrite M.find_merge by reflexivity. rewrite M.find_empty.
    destruct (M.find p m) as [row|].
    - exact (find_shift_column_row target d row q).
    - cbn [shift_column_row row_of]. rewrite M.find_empty. reflexivity.
  Qed.

  (** The column pass creates and removes no finite coordinates. *)
  Lemma raw_entry_shift_columns_presence : forall (target : K.t) d m p q,
    raw_entry (shift_columns target d m) p q <> None <-> raw_entry m p q <> None.
  Proof.
    intros target d m p q. rewrite raw_entry_shift_columns. apply shift_option_presence.
  Qed.

  (** Column translation preserves raw support, including inconsistent labels. *)
  Lemma support_shift_columns : forall (target : K.t) d m p,
    In p (support (shift_columns target d m)) <-> In p (support m).
  Proof.
    intros target d m. apply support_by_presence.
    - apply find_shift_columns_presence.
    - apply raw_entry_shift_columns_presence.
  Qed.

  (** Column translation retains both support size and encoded-key bit allowance. *)
  Lemma shift_columns_sizes : forall (target : K.t) d m,
    supp (shift_columns target d m) = supp m /\ b (shift_columns target d m) = b m.
  Proof.
    intros target d m. apply support_sizes, support_shift_columns.
  Qed.

  (** Adding the translation to existing entries uses one additional carry bit. *)
  Lemma ell_shift_columns : forall (target : K.t) d m,
    ell (shift_columns target d m) <= ell m + Z.size_nat d + 1.
  Proof.
    intros target d m. apply ell_bound. intros p q z Hentry.
    rewrite raw_entry_shift_columns in Hentry.
    destruct (raw_entry m p q) as [old|] eqn:Hraw; [|discriminate].
    pose proof (ell_entry m p q old Hraw) as Hold.
    destruct (Pos.eqb q (K.encode target)) eqn:Hselected;
      cbn [option_map] in Hentry; injection Hentry as <-.
    - eapply Nat.le_trans; [apply zbits_add_sum|]. lia.
    - lia.
  Qed.

  (** Subtraction has the same additive bit allowance as addition with an opposite. *)
  Lemma zbits_sub_sum : forall a d,
    Z.size_nat (a - d)%Z <= Z.size_nat a + Z.size_nat d + 1.
  Proof.
    intros a d. pose proof (zbits_add_sum a (-d)%Z) as Hbits.
    rewrite zbits_opp in Hbits. exact Hbits.
  Qed.

  (** The row pass updates only a row already present after the column pass. *)
  Lemma find_shift_literal_presence : forall (target : K.t) d m p,
    M.find p (shift_literal target d m) <> None <-> M.find p m <> None.
  Proof.
    intros target d m p. rewrite <- (find_shift_columns_presence target d m p).
    unfold shift_literal. set (next := shift_columns target d m).
    destruct (M.get target next) as [row|] eqn:Hrow; [|reflexivity].
    rewrite M.find_set. destruct (Pos.eqb p (K.encode target)) eqn:Hsame.
    - apply Pos.eqb_eq in Hsame. subst p.
      rewrite <- (M.get_find (M.t Z) target next), Hrow.
      split; intros _ H; discriminate H.
    - reflexivity.
  Qed.

  (** The final row translation subtracts its offset at the selected raw source code. *)
  Lemma raw_entry_shift_literal : forall (target : K.t) d m p q,
    raw_entry (shift_literal target d m) p q =
      if Pos.eqb p (K.encode target) then
        option_map (fun z => (z - d)%Z) (raw_entry (shift_columns target d m) p q)
      else raw_entry (shift_columns target d m) p q.
  Proof.
    intros target d m p q. unfold shift_literal.
    set (next := shift_columns target d m).
    destruct (M.get target next) as [row|] eqn:Hrow.
    - unfold raw_entry at 1. rewrite M.find_set.
      destruct (Pos.eqb p (K.encode target)) eqn:Hsame.
      + apply Pos.eqb_eq in Hsame. subst p. cbn [row_of].
        rewrite M.find_merge by reflexivity. rewrite M.find_empty.
        unfold raw_entry. rewrite <- (M.get_find (M.t Z) target next), Hrow.
        cbn [row_of shift_bound]. destruct (M.find q row); reflexivity.
      + reflexivity.
    - destruct (Pos.eqb p (K.encode target)) eqn:Hsame; [|reflexivity].
      apply Pos.eqb_eq in Hsame. subst p.
      unfold raw_entry. rewrite <- (M.get_find (M.t Z) target next), Hrow.
      cbn [row_of]. rewrite M.find_empty. reflexivity.
  Qed.

  (** A complete literal translation preserves every finite coordinate. *)
  Lemma raw_entry_shift_literal_presence : forall (target : K.t) d m p q,
    raw_entry (shift_literal target d m) p q <> None <-> raw_entry m p q <> None.
  Proof.
    intros target d m p q. rewrite raw_entry_shift_literal.
    destruct (Pos.eqb p (K.encode target)).
    - rewrite shift_option_presence. apply raw_entry_shift_columns_presence.
    - apply raw_entry_shift_columns_presence.
  Qed.

  (** A complete literal translation preserves raw support membership. *)
  Lemma support_shift_literal : forall (target : K.t) d m p,
    In p (support (shift_literal target d m)) <-> In p (support m).
  Proof.
    intros target d m. apply support_by_presence.
    - apply find_shift_literal_presence.
    - apply raw_entry_shift_literal_presence.
  Qed.

  (** Literal translation retains support size and its key-bit maximum. *)
  Lemma shift_literal_sizes : forall (target : K.t) d m,
    supp (shift_literal target d m) = supp m /\ b (shift_literal target d m) = b m.
  Proof.
    intros target d m. apply support_sizes, support_shift_literal.
  Qed.

  (** Two translation passes add at most two offset allowances and two carry bits. *)
  Lemma ell_shift_literal : forall (target : K.t) d m,
    ell (shift_literal target d m) <= ell m + 2 * Z.size_nat d + 2.
  Proof.
    intros target d m. pose proof (ell_shift_columns target d m) as Hcolumns.
    apply ell_bound. intros p q z Hentry. rewrite raw_entry_shift_literal in Hentry.
    destruct (Pos.eqb p (K.encode target)).
    - destruct (raw_entry (shift_columns target d m) p q) as [old|] eqn:Hraw;
        [|discriminate].
      cbn [option_map] in Hentry. injection Hentry as <-.
      pose proof (ell_entry (shift_columns target d m) p q old Hraw) as Hold.
      pose proof (zbits_sub_sum old d). lia.
    - pose proof (ell_entry (shift_columns target d m) p q z Hentry). lia.
  Qed.

  (** Signed shifts charge sparse columns and the selected literal row. *)

Definition shift_column_work (target : K.t) (d : Z) (row : M.t Z) : nat :=
    K.bits target + Z.size_nat d +
      option_weight Z.size_nat (M.get target row) + 1.

  Lemma T_shift_column_row_le : forall target d a b,
    (T_shift_column_row target d a b <= 8 * (M.c_map + 1) *
      N.of_nat (option_weight (shift_column_work target d) a + 1))%N.
  Proof.
    intros target d [row|] ignored.
    - cbn [option_weight]. unfold shift_column_work.
      destruct (M.get target row) as [old|] eqn:Hentry;
        unfold T_shift_column_row; cbn beta iota zeta; rewrite Hentry;
        cbn [option_weight]; time_step.
    - time_step.
  Qed.

  Lemma T_shift_bound_le : forall d a b,
    (T_shift_bound d a b <= 8 *
      N.of_nat (option_weight (fun z => (Z.size_nat d + Z.size_nat z + 1)%nat) a + 1))%N.
  Proof.
    intros d [z|] ignored; unfold option_weight; time_step.
  Qed.

  Lemma shift_linear_budget : forall n payload factor,
    1 <= payload -> 1 <= factor ->
    n * (factor * payload) + 1 <= factor * ((n + 1)^2 * payload).
  Proof.
    intros n payload factor Hpayload Hfactor.
    assert (Hpositive : 1 <= factor * payload) by nia.
    eapply Nat.le_trans with ((n + 1) * (factor * payload)); [nia|].
    replace (factor * ((n + 1)^2 * payload)) with
      ((n + 1)^2 * (factor * payload)) by ring.
    apply Nat.mul_le_mono_r. cbn [Nat.pow]. nia.
  Qed.

  Lemma shift_column_work_bound : forall target d m,
    code_work (shift_column_work target d) m + 1 <=
      3 * ((supp m + 1)^2 *
        (b m + ell m + K.bits target + Z.size_nat d + 1)).
  Proof.
    intros target d m.
    assert (Hsupport : forall p, In p (M.codes m) -> In p (support m)).
    { intros p Hp. apply support_spec. now left. }
    pose proof (nodes_support (M.t Z) m m Hsupport) as Hnodes.
    pose proof (codes_support_length (M.t Z) m m Hsupport) as Hcount.
    assert (Hstored : stored_weight (shift_column_work target d) m <=
      length (M.codes m) * (K.bits target + Z.size_nat d + ell m + 1)).
    { apply stored_weight_uniform. intros p row Hrow.
      unfold shift_column_work.
      destruct (M.get target row) as [old|] eqn:Hentry; cbn [option_weight].
      - pose proof (row_get_bits m p row target old Hrow Hentry). lia.
      - lia. }
    assert (Hstored' : stored_weight (shift_column_work target d) m <=
      supp m * (K.bits target + Z.size_nat d + ell m + 1)).
    { eapply Nat.le_trans; [exact Hstored|]. now apply Nat.mul_le_mono_r. }
    set (payload := b m + ell m + K.bits target + Z.size_nat d + 1).
    assert (Hpayload : 1 <= payload) by (unfold payload; lia).
    assert (Hscalar : b m + ell m + K.bits target + Z.size_nat d + 3 <=
      3 * payload) by (unfold payload; lia).
    assert (Hwork : code_work (shift_column_work target d) m + 1 <=
      supp m * (3 * payload) + 1).
    { pose proof (Nat.mul_le_mono_l _ _ (supp m) Hscalar) as Hscaled.
      unfold code_work. nia. }
    eapply Nat.le_trans; [exact Hwork|].
    apply shift_linear_budget; lia.
  Qed.

  Lemma shift_selected_row_work_bound : forall target d m row,
    M.get target (shift_columns target d m) = Some row ->
    code_work (fun z => (Z.size_nat d + Z.size_nat z + 1)%nat) row + 1 <=
      4 * ((supp m + 1)^2 *
        (b m + ell m + K.bits target + Z.size_nat d + 1)).
  Proof.
    intros target d m row Hrow.
    set (next := shift_columns target d m). fold next in Hrow.
    assert (Hsupport : forall p, In p (M.codes row) -> In p (support next)).
    { intros p Hp. apply (row_lookup_support next target p).
      rewrite Hrow. exact Hp. }
    assert (Hbits : forall p z, M.find p row = Some z -> Z.size_nat z <= ell next).
    { intros p z Hz. apply (row_lookup_bits next target p z).
      rewrite Hrow. exact Hz. }
    pose proof (code_work_bits_bound next row (Z.size_nat d) (ell next)
      Hsupport Hbits) as Hrow_work.
    destruct (shift_columns_sizes target d m) as [Hcount Hkeys].
    pose proof (ell_shift_columns target d m) as Hell.
    fold next in Hcount, Hkeys, Hell. rewrite Hcount, Hkeys in Hrow_work.
    set (payload := b m + ell m + K.bits target + Z.size_nat d + 1).
    assert (Hpayload : 1 <= payload) by (unfold payload; lia).
    assert (Hscalar : b m + ell next + Z.size_nat d + 3 <= 4 * payload).
    { unfold payload. lia. }
    assert (Hwork : code_work (fun z => (Z.size_nat d + Z.size_nat z + 1)%nat)
      row + 1 <= supp m * (4 * payload) + 1).
    { pose proof (Nat.mul_le_mono_l _ _ (supp m) Hscalar). lia. }
    eapply Nat.le_trans; [exact Hwork|]. apply shift_linear_budget; lia.
  Qed.

  Lemma T_shift_columns_le : forall target d m,
    (T_shift_columns target d m <= 64 * (M.c_map + 1) * (M.c_map + 1) *
      N.of_nat ((supp m + 1)^2 *
        (b m + ell m + K.bits target + Z.size_nat d + 1)))%N.
  Proof.
    intros target d m.
    set (units := (supp m + 1)^2 *
      (b m + ell m + K.bits target + Z.size_nat d + 1)).
    change (T_shift_columns target d m <=
      64 * (M.c_map + 1) * (M.c_map + 1) * N.of_nat units)%N.
    assert (Hpositive : 1 <= units).
    { unfold units. eapply Nat.le_trans; [|apply quadratic_payload_le]. lia. }
    pose proof (time_of_nat_le _ _ Hpositive) as Hwork.
    pose proof (shift_column_work_bound target d m) as Hdata.
    change (code_work (shift_column_work target d) m + 1 <= 3 * units) in Hdata.
    pose proof (time_of_nat_le _ _ Hdata) as HdataN.
    rewrite (Nat2N.inj_mul 3 units) in HdataN.
    set (work := N.of_nat units) in *.
    change (1 <= work)%N in Hwork.
    pose proof (T_merge_left_code_work (M.t Z) (M.t Z) (M.t Z)
      (shift_column_row target d) (fun a b => T_shift_column_row target d a b)
      (shift_column_work target d) m (8 * (M.c_map + 1))%N
      (T_shift_column_row_le target d)) as Hmerge.
    assert (Hmerge_work : (M.T_merge (shift_column_row target d)
      (fun a b => T_shift_column_row target d a b) m M.empty <=
      M.c_map * (8 * (M.c_map + 1) + 1) * 2 * (3 * work))%N).
    { eapply N.le_trans; [exact Hmerge|].
      apply N.mul_le_mono_l. exact HdataN. }
    assert (Hcoefficient :
      (M.c_map * (8 * (M.c_map + 1) + 1) * 2 * 3 + 1 <=
        64 * (M.c_map + 1) * (M.c_map + 1))%N).
    { pose proof (N.le_0_l M.c_map) as Hmap. clear -Hmap. nia. }
    pose proof (N.mul_le_mono_r _ _ work Hcoefficient) as Hbudget.
    rewrite N.mul_add_distr_r, N.mul_1_l in Hbudget.
    replace (M.c_map * (8 * (M.c_map + 1) + 1) * 2 * (3 * work))%N with
      ((M.c_map * (8 * (M.c_map + 1) + 1) * 2 * 3) * work)%N
      in Hmerge_work by ring.
    unfold T_shift_columns. cbn beta iota zeta.
    clearbody work. clear - Hmerge_work Hwork Hbudget. lia.
  Qed.

  Lemma T_shift_literal_le : forall target d m,
    (T_shift_literal target d m <= 256 * (M.c_map + 1) * (M.c_map + 1) *
      N.of_nat ((supp m + 1)^2 *
        (b m + ell m + K.bits target + Z.size_nat d + 1)))%N.
  Proof.
    intros target d m.
    set (units := (supp m + 1)^2 *
      (b m + ell m + K.bits target + Z.size_nat d + 1)).
    change (T_shift_literal target d m <=
      256 * (M.c_map + 1) * (M.c_map + 1) * N.of_nat units)%N.
    set (next := shift_columns target d m).
    assert (Hkey : K.bits target + 1 <= units).
    { unfold units. eapply Nat.le_trans; [|apply quadratic_payload_le]. lia. }
    assert (Hpositive : 1 <= units) by lia.
    pose proof (time_of_nat_le _ _ Hkey) as HkeyN.
    pose proof (time_of_nat_le _ _ Hpositive) as Hwork.
    pose proof (T_shift_columns_le target d m) as Hcolumns.
    change (T_shift_columns target d m <=
      64 * (M.c_map + 1) * (M.c_map + 1) * N.of_nat units)%N in Hcolumns.
    set (work := N.of_nat units) in *.
    change (1 <= work)%N in Hwork.
    assert (Hget : (M.T_get target next <= M.c_map * work)%N).
    { eapply N.le_trans; [apply M.T_get_le|].
      apply N.mul_le_mono_l. exact HkeyN. }
    assert (Hcoefficient :
      (64 * (M.c_map + 1) * (M.c_map + 1) + M.c_map +
        M.c_map * (8 + 1) * 2 * 4 + M.c_map + 4 <=
        256 * (M.c_map + 1) * (M.c_map + 1))%N).
    { pose proof (N.le_0_l M.c_map) as Hmap. clear -Hmap. nia. }
    pose proof (N.mul_le_mono_r _ _ work Hcoefficient) as Hbudget.
    repeat rewrite N.mul_add_distr_r in Hbudget.
    destruct (M.get target next) as [row|] eqn:Hrow.
    - assert (Hdata : code_work
        (fun z => (Z.size_nat d + Z.size_nat z + 1)%nat) row + 1 <= 4 * units).
      { unfold units. apply shift_selected_row_work_bound. exact Hrow. }
      pose proof (time_of_nat_le _ _ Hdata) as HdataN.
      rewrite (Nat2N.inj_mul 4 units) in HdataN. fold work in HdataN.
      pose proof (T_merge_left_code_work Z Z Z (shift_bound d)
        (fun a b => T_shift_bound d a b)
        (fun z => (Z.size_nat d + Z.size_nat z + 1)%nat)
        row 8%N (T_shift_bound_le d)) as Hmerge.
      assert (Hmerge_work : (M.T_merge (shift_bound d)
        (fun a b => T_shift_bound d a b) row M.empty <=
        M.c_map * (8 + 1) * 2 * (4 * work))%N).
      { eapply N.le_trans; [exact Hmerge|].
        apply N.mul_le_mono_l. exact HdataN. }
      assert (Hset : (M.T_set target
        (M.merge (shift_bound d) row M.empty) next <= M.c_map * work)%N).
      { eapply N.le_trans; [apply M.T_set_le|].
        apply N.mul_le_mono_l. exact HkeyN. }
      replace (M.c_map * (8 + 1) * 2 * (4 * work))%N with
        ((M.c_map * (8 + 1) * 2 * 4) * work)%N in Hmerge_work by ring.
      unfold T_shift_literal. cbn beta iota zeta. fold next. rewrite Hrow.
      cbn beta iota zeta. time_simpl.
      clearbody work. clear - Hcolumns Hget Hset Hmerge_work Hbudget Hwork. lia.
    - unfold T_shift_literal. cbn beta iota zeta. fold next. rewrite Hrow.
      cbn beta iota zeta. time_simpl.
      clearbody work. clear - Hcolumns Hget Hbudget Hwork. lia.
  Qed.

  (** Both signed literal translations fit the original assignment payload allowance. *)
  Lemma T_shift_le : forall x d m,
    (T_shift x d m <= 2048 * (M.c_map + 1) * (M.c_map + 1) *
      N.of_nat ((supp m + 1)^2 *
        (b m + ell m + X.bits x + Z.size_nat d + 1)))%N.
  Proof.
    intros x d m.
    set (units := (supp m + 1)^2 *
      (b m + ell m + X.bits x + Z.size_nat d + 1)).
    set (work := N.of_nat units).
    assert (Hpositive : 1 <= units).
    { unfold units. eapply Nat.le_trans; [|apply quadratic_payload_le]. lia. }
    pose proof (time_of_nat_le _ _ Hpositive) as Hwork.
    change (1 <= work)%N in Hwork.
    assert (Hfirst_nat : (supp m + 1)^2 *
      (b m + ell m + K.bits (x, true) + Z.size_nat d + 1) <= 2 * units).
    { unfold units. rewrite literal_bits. cbn beta iota zeta.
      replace (2 * ((supp m + 1)^2 *
        (b m + ell m + X.bits x + Z.size_nat d + 1))) with
        ((supp m + 1)^2 * (2 * (b m + ell m + X.bits x + Z.size_nat d + 1))) by ring.
      apply Nat.mul_le_mono_l. lia. }
    assert (Hfirst : (T_shift_literal (x, true) d m <=
      512 * (M.c_map + 1) * (M.c_map + 1) * work)%N).
    { eapply N.le_trans; [apply T_shift_literal_le|].
      replace (512 * (M.c_map + 1) * (M.c_map + 1) * work)%N with
        (256 * (M.c_map + 1) * (M.c_map + 1) * (2 * work))%N by ring.
      apply N.mul_le_mono_l.
      pose proof (time_of_nat_le _ _ Hfirst_nat) as Hcast.
      rewrite (Nat2N.inj_mul 2 units) in Hcast. exact Hcast. }
    set (first := shift_literal (x, true) d m).
    destruct (shift_literal_sizes (x, true) d m) as [Hcount Hkeys].
    pose proof (ell_shift_literal (x, true) d m) as Hell.
    fold first in Hcount, Hkeys, Hell.
    assert (Hsecond_nat : (supp first + 1)^2 *
      (b first + ell first + K.bits (x, false) + Z.size_nat (-d)%Z + 1) <= 3 * units).
    { unfold units. rewrite Hcount, Hkeys, literal_bits, zbits_opp.
      cbn beta iota zeta.
      replace (3 * ((supp m + 1)^2 *
        (b m + ell m + X.bits x + Z.size_nat d + 1))) with
        ((supp m + 1)^2 * (3 * (b m + ell m + X.bits x + Z.size_nat d + 1))) by ring.
      apply Nat.mul_le_mono_l. lia. }
    assert (Hsecond : (T_shift_literal (x, false) (-d)%Z first <=
      768 * (M.c_map + 1) * (M.c_map + 1) * work)%N).
    { eapply N.le_trans; [apply T_shift_literal_le|].
      replace (768 * (M.c_map + 1) * (M.c_map + 1) * work)%N with
        (256 * (M.c_map + 1) * (M.c_map + 1) * (3 * work))%N by ring.
      apply N.mul_le_mono_l.
      pose proof (time_of_nat_le _ _ Hsecond_nat) as Hcast.
      rewrite (Nat2N.inj_mul 3 units) in Hcast. exact Hcast. }
    pose proof (Z.T_opp_le d) as Hopp.
    assert (Hcoefficient :
      (512 * (M.c_map + 1) * (M.c_map + 1) +
        768 * (M.c_map + 1) * (M.c_map + 1) + 2 <=
        2048 * (M.c_map + 1) * (M.c_map + 1))%N).
    { pose proof (N.le_0_l M.c_map) as Hmap. clear -Hmap. nia. }
    pose proof (N.mul_le_mono_r _ _ work Hcoefficient) as Hbudget.
    repeat rewrite N.mul_add_distr_r in Hbudget.
    match goal with
    | |- N.le ?clock _ =>
      change (clock <= 2048 * (M.c_map + 1) * (M.c_map + 1) * work)%N
    end.
    unfold T_shift. cbn beta iota zeta. fold first. time_simpl.
    clearbody work. clear - Hfirst Hsecond Hopp Hbudget Hwork. lia.
  Qed.

  (** Raw optional insertion changes exactly the supplied target code. *)
  Lemma find_put_bound_raw : forall target bound row p,
    M.find p (put_bound target bound row) =
      if Pos.eqb p (K.encode target) then bound else M.find p row.
  Proof.
    intros target [z|] row p; unfold put_bound.
    - apply M.find_set.
    - apply M.find_remove.
  Qed.

  Local Definition copy_column_matrix (target source : K.t) (d : Z) (m : dbm) : dbm :=
    M.merge (copy_column_row target source d) m M.empty.

  (** Copying a column retains the source matrix's outer rows. *)
  Lemma find_copy_column_matrix : forall target source d m p,
    M.find p (copy_column_matrix target source d m) =
      match M.find p m with
      | Some row => Some (put_bound target (edge_prefix d (M.get source row)) row)
      | None => None
      end.
  Proof.
    intros target source d m p. unfold copy_column_matrix.
    rewrite M.find_merge by reflexivity. rewrite M.find_empty.
    destruct (M.find p m); reflexivity.
  Qed.

  (** Every copied column entry comes from its source column and offset. *)
  Lemma raw_copy_column_matrix : forall target source d m p q,
    raw_entry (copy_column_matrix target source d m) p q =
      if Pos.eqb q (K.encode target) then
        edge_prefix d (raw_entry m p (K.encode source))
      else raw_entry m p q.
  Proof.
    intros target source d m p q. unfold raw_entry at 1.
    rewrite find_copy_column_matrix. unfold raw_entry.
    destruct (M.find p m) as [row|]; cbn [row_of].
    - rewrite find_put_bound_raw, M.get_find. reflexivity.
    - rewrite !M.find_empty. destruct (Pos.eqb q (K.encode target)); reflexivity.
  Qed.

  (** Copying a column introduces no code other than the target. *)
  Lemma support_copy_column_matrix : forall target source d m p,
    In p (support (copy_column_matrix target source d m)) ->
      p = K.encode target \/ In p (support m).
  Proof.
    intros target source d m p Hp. apply support_find in Hp.
    destruct Hp as [Hrow|[q Hentry]].
    - right. apply support_find. left. rewrite find_copy_column_matrix in Hrow.
      destruct (M.find p m); congruence.
    - rewrite raw_copy_column_matrix in Hentry.
      destruct (Pos.eqb p (K.encode target)) eqn:Htarget.
      + left. now apply Pos.eqb_eq.
      + right. apply support_find. right. now exists q.
  Qed.

  (** Column copying adds at most the target's signed endpoint allowance. *)
  Lemma copy_column_matrix_sizes : forall target source d m,
    supp (copy_column_matrix target source d m) <= supp m + 4 /\
    b (copy_column_matrix target source d m) <= b m + K.bits target + 1.
  Proof.
    intros target source d m.
    assert (Hsupport : forall p, In p (support (copy_column_matrix target source d m)) ->
      p = K.encode target \/ p = K.encode target \/ p = K.encode (flip target) \/
        p = K.encode (flip target) \/ In p (support m)).
    { intros p Hp. pose proof (support_copy_column_matrix target source d m p Hp). tauto. }
    destruct (support_signed_endpoints target target _ m Hsupport) as [Hcount Hbits].
    split; [exact Hcount|]. rewrite Nat.max_id in Hbits.
    eapply Nat.le_trans; [exact Hbits|]. apply Nat.max_lub; lia.
  Qed.

  (** A copied column adds one offset and one carry bit to the payload bound. *)
  Lemma ell_copy_column_matrix : forall target source d m,
    ell (copy_column_matrix target source d m) <= ell m + Z.size_nat d + 1.
  Proof.
    intros target source d m. apply ell_bound. intros p q z Hentry.
    rewrite raw_copy_column_matrix in Hentry.
    destruct (Pos.eqb q (K.encode target)).
    - destruct (raw_entry m p (K.encode source)) as [a|] eqn:Hsource; [|discriminate].
      cbn [edge_prefix] in Hentry. injection Hentry as <-.
      pose proof (ell_entry m p (K.encode source) a Hsource).
      pose proof (zbits_add_sum a d). lia.
    - pose proof (ell_entry m p q z Hentry). lia.
  Qed.

  (** The new target row is the shifted source row after the column copy. *)
  Lemma raw_copy_literal : forall target source d m p q,
    raw_entry (copy_literal target source d m) p q =
      if Pos.eqb p (K.encode target) then
        option_map (fun z => (z - d)%Z)
          (raw_entry (copy_column_matrix target source d m) (K.encode source) q)
      else raw_entry (copy_column_matrix target source d m) p q.
  Proof.
    intros target source d m p q. unfold copy_literal.
    fold (copy_column_matrix target source d m). unfold raw_entry at 1.
    rewrite M.find_set. destruct (Pos.eqb p (K.encode target)); [|reflexivity].
    cbn [row_of]. rewrite M.find_merge by reflexivity. rewrite M.find_empty.
    unfold raw_entry. rewrite M.get_find.
    destruct (M.find q (row_of (M.find (K.encode source)
      (copy_column_matrix target source d m)))); reflexivity.
  Qed.

  (** The target row is the only new outer row of a literal copy. *)
  Lemma find_copy_literal_presence : forall target source d m p,
    M.find p (copy_literal target source d m) <> None <->
      p = K.encode target \/ M.find p m <> None.
  Proof.
    intros target source d m p. unfold copy_literal.
    fold (copy_column_matrix target source d m). rewrite M.find_set.
    destruct (Pos.eqb p (K.encode target)) eqn:Htarget.
    - apply Pos.eqb_eq in Htarget. split; [intros; now left|intros; discriminate].
    - apply Pos.eqb_neq in Htarget. rewrite find_copy_column_matrix.
      destruct (M.find p m); split; intuition congruence.
  Qed.

  (** Literal copying introduces no supported code except its target. *)
  Lemma support_copy_literal : forall target source d m p,
    In p (support (copy_literal target source d m)) ->
      p = K.encode target \/ In p (support m).
  Proof.
    intros target source d m p Hp. apply support_find in Hp.
    destruct Hp as [Hrow|[q Hentry]].
    - apply find_copy_literal_presence in Hrow. destruct Hrow as [Htarget|Hrow].
      + now left.
      + right. apply support_find. now left.
    - rewrite raw_copy_literal in Hentry.
      apply (support_copy_column_matrix target source d m p).
      apply support_find. right.
      destruct (Pos.eqb q (K.encode target)).
      + apply shift_option_presence in Hentry. now exists (K.encode source).
      + now exists q.
  Qed.

  (** One literal copy has bounded support and key-width growth. *)
  Lemma copy_literal_sizes : forall target source d m,
    supp (copy_literal target source d m) <= supp m + 4 /\
    b (copy_literal target source d m) <= b m + K.bits target + 1.
  Proof.
    intros target source d m.
    assert (Hsupport : forall p, In p (support (copy_literal target source d m)) ->
      p = K.encode target \/ p = K.encode target \/ p = K.encode (flip target) \/
        p = K.encode (flip target) \/ In p (support m)).
    { intros p Hp. pose proof (support_copy_literal target source d m p Hp). tauto. }
    destruct (support_signed_endpoints target target _ m Hsupport) as [Hcount Hbits].
    split; [exact Hcount|]. rewrite Nat.max_id in Hbits.
    eapply Nat.le_trans; [exact Hbits|]. apply Nat.max_lub; lia.
  Qed.

  (** A literal copy adds at most two offset allowances to every finite entry. *)
  Lemma ell_copy_literal : forall target source d m,
    ell (copy_literal target source d m) <= ell m + 2 * Z.size_nat d + 2.
  Proof.
    intros target source d m.
    pose proof (ell_copy_column_matrix target source d m) as Hell.
    apply ell_bound. intros p q z Hentry. rewrite raw_copy_literal in Hentry.
    destruct (Pos.eqb p (K.encode target)).
    - destruct (raw_entry (copy_column_matrix target source d m) (K.encode source) q)
        as [a|] eqn:Hsource; [|discriminate].
      cbn [option_map] in Hentry. injection Hentry as <-.
      pose proof (ell_entry _ _ _ a Hsource). pose proof (zbits_sub_sum a d). lia.
    - pose proof (ell_entry _ _ _ z Hentry). lia.
  Qed.

  (** A linear support allowance includes one full payload charge. *)
  Lemma linear_payload_le : forall n payload, payload <= (n + 1) * payload.
  Proof.
    intros n payload. nia.
  Qed.

  (** A positive unit of setup cost fits one additional support item. *)
  Lemma shift_support_budget : forall n payload factor,
    1 <= payload -> 1 <= factor ->
    n * (factor * payload) + 1 <= factor * ((n + 1) * payload).
  Proof.
    intros n payload factor Hpayload Hfactor.
    assert (Hpositive : 1 <= factor * payload) by nia.
    eapply Nat.le_trans with ((n + 1) * (factor * payload)); [nia|].
    replace (factor * ((n + 1) * payload)) with
      ((n + 1) * (factor * payload)) by ring.
    apply Nat.mul_le_mono_r. cbn [Nat.pow]. nia.
  Qed.

  (** Column translation visits each stored row once. *)
  Lemma shift_column_work_linear : forall target d m,
    code_work (shift_column_work target d) m + 1 <=
      3 * ((supp m + 1) *
        (b m + ell m + K.bits target + Z.size_nat d + 1)).
  Proof.
    intros target d m.
    assert (Hsupport : forall p, In p (M.codes m) -> In p (support m)).
    { intros p Hp. apply support_spec. now left. }
    pose proof (nodes_support (M.t Z) m m Hsupport) as Hnodes.
    pose proof (codes_support_length (M.t Z) m m Hsupport) as Hcount.
    assert (Hstored : stored_weight (shift_column_work target d) m <=
      length (M.codes m) * (K.bits target + Z.size_nat d + ell m + 1)).
    { apply stored_weight_uniform. intros p row Hrow.
      unfold shift_column_work.
      destruct (M.get target row) as [old|] eqn:Hentry; cbn [option_weight].
      - pose proof (row_get_bits m p row target old Hrow Hentry). lia.
      - lia. }
    assert (Hstored' : stored_weight (shift_column_work target d) m <=
      supp m * (K.bits target + Z.size_nat d + ell m + 1)).
    { eapply Nat.le_trans; [exact Hstored|]. now apply Nat.mul_le_mono_r. }
    set (payload := b m + ell m + K.bits target + Z.size_nat d + 1).
    assert (Hpayload : 1 <= payload) by (unfold payload; lia).
    assert (Hscalar : b m + ell m + K.bits target + Z.size_nat d + 3 <=
      3 * payload) by (unfold payload; lia).
    assert (Hwork : code_work (shift_column_work target d) m + 1 <=
      supp m * (3 * payload) + 1).
    { pose proof (Nat.mul_le_mono_l _ _ (supp m) Hscalar) as Hscaled.
      unfold code_work. nia. }
    eapply Nat.le_trans; [exact Hwork|].
    apply shift_support_budget; lia.
  Qed.

  (** The translated source row has only linear support work. *)
  Lemma shift_selected_row_work_linear : forall target d m row,
    M.get target (shift_columns target d m) = Some row ->
    code_work (fun z => (Z.size_nat d + Z.size_nat z + 1)%nat) row + 1 <=
      4 * ((supp m + 1) *
        (b m + ell m + K.bits target + Z.size_nat d + 1)).
  Proof.
    intros target d m row Hrow.
    set (next := shift_columns target d m). fold next in Hrow.
    assert (Hsupport : forall p, In p (M.codes row) -> In p (support next)).
    { intros p Hp. apply (row_lookup_support next target p).
      rewrite Hrow. exact Hp. }
    assert (Hbits : forall p z, M.find p row = Some z -> Z.size_nat z <= ell next).
    { intros p z Hz. apply (row_lookup_bits next target p z).
      rewrite Hrow. exact Hz. }
    pose proof (code_work_bits_bound next row (Z.size_nat d) (ell next)
      Hsupport Hbits) as Hrow_work.
    destruct (shift_columns_sizes target d m) as [Hcount Hkeys].
    pose proof (ell_shift_columns target d m) as Hell.
    fold next in Hcount, Hkeys, Hell. rewrite Hcount, Hkeys in Hrow_work.
    set (payload := b m + ell m + K.bits target + Z.size_nat d + 1).
    assert (Hpayload : 1 <= payload) by (unfold payload; lia).
    assert (Hscalar : b m + ell next + Z.size_nat d + 3 <= 4 * payload).
    { unfold payload. lia. }
    assert (Hwork : code_work (fun z => (Z.size_nat d + Z.size_nat z + 1)%nat)
      row + 1 <= supp m * (4 * payload) + 1).
    { pose proof (Nat.mul_le_mono_l _ _ (supp m) Hscalar). lia. }
    eapply Nat.le_trans; [exact Hwork|]. apply shift_support_budget; lia.
  Qed.

  (** Column translation has linear support cost with bit-priced callbacks. *)
  Lemma T_shift_columns_linear : forall target d m,
    (T_shift_columns target d m <= 64 * (M.c_map + 1) * (M.c_map + 1) *
      N.of_nat ((supp m + 1) *
        (b m + ell m + K.bits target + Z.size_nat d + 1)))%N.
  Proof.
    intros target d m.
    set (units := (supp m + 1) *
      (b m + ell m + K.bits target + Z.size_nat d + 1)).
    change (T_shift_columns target d m <=
      64 * (M.c_map + 1) * (M.c_map + 1) * N.of_nat units)%N.
    assert (Hpositive : 1 <= units).
    { unfold units. eapply Nat.le_trans; [|apply linear_payload_le]. lia. }
    pose proof (time_of_nat_le _ _ Hpositive) as Hwork.
    pose proof (shift_column_work_linear target d m) as Hdata.
    change (code_work (shift_column_work target d) m + 1 <= 3 * units) in Hdata.
    pose proof (time_of_nat_le _ _ Hdata) as HdataN.
    rewrite (Nat2N.inj_mul 3 units) in HdataN.
    set (work := N.of_nat units) in *.
    change (1 <= work)%N in Hwork.
    pose proof (T_merge_left_code_work (M.t Z) (M.t Z) (M.t Z)
      (shift_column_row target d) (fun a b => T_shift_column_row target d a b)
      (shift_column_work target d) m (8 * (M.c_map + 1))%N
      (T_shift_column_row_le target d)) as Hmerge.
    assert (Hmerge_work : (M.T_merge (shift_column_row target d)
      (fun a b => T_shift_column_row target d a b) m M.empty <=
      M.c_map * (8 * (M.c_map + 1) + 1) * 2 * (3 * work))%N).
    { eapply N.le_trans; [exact Hmerge|].
      apply N.mul_le_mono_l. exact HdataN. }
    assert (Hcoefficient :
      (M.c_map * (8 * (M.c_map + 1) + 1) * 2 * 3 + 1 <=
        64 * (M.c_map + 1) * (M.c_map + 1))%N).
    { pose proof (N.le_0_l M.c_map) as Hmap. clear -Hmap. nia. }
    pose proof (N.mul_le_mono_r _ _ work Hcoefficient) as Hbudget.
    rewrite N.mul_add_distr_r, N.mul_1_l in Hbudget.
    replace (M.c_map * (8 * (M.c_map + 1) + 1) * 2 * (3 * work))%N with
      ((M.c_map * (8 * (M.c_map + 1) + 1) * 2 * 3) * work)%N
      in Hmerge_work by ring.
    unfold T_shift_columns. cbn beta iota zeta.
    clearbody work. clear - Hmerge_work Hwork Hbudget. lia.
  Qed.

  (** A literal translation adds one source-row traversal to its column pass. *)
  Lemma T_shift_literal_linear : forall target d m,
    (T_shift_literal target d m <= 256 * (M.c_map + 1) * (M.c_map + 1) *
      N.of_nat ((supp m + 1) *
        (b m + ell m + K.bits target + Z.size_nat d + 1)))%N.
  Proof.
    intros target d m.
    set (units := (supp m + 1) *
      (b m + ell m + K.bits target + Z.size_nat d + 1)).
    change (T_shift_literal target d m <=
      256 * (M.c_map + 1) * (M.c_map + 1) * N.of_nat units)%N.
    set (next := shift_columns target d m).
    assert (Hkey : K.bits target + 1 <= units).
    { unfold units. eapply Nat.le_trans; [|apply linear_payload_le]. lia. }
    assert (Hpositive : 1 <= units) by lia.
    pose proof (time_of_nat_le _ _ Hkey) as HkeyN.
    pose proof (time_of_nat_le _ _ Hpositive) as Hwork.
    pose proof (T_shift_columns_linear target d m) as Hcolumns.
    change (T_shift_columns target d m <=
      64 * (M.c_map + 1) * (M.c_map + 1) * N.of_nat units)%N in Hcolumns.
    set (work := N.of_nat units) in *.
    change (1 <= work)%N in Hwork.
    assert (Hget : (M.T_get target next <= M.c_map * work)%N).
    { eapply N.le_trans; [apply M.T_get_le|].
      apply N.mul_le_mono_l. exact HkeyN. }
    assert (Hcoefficient :
      (64 * (M.c_map + 1) * (M.c_map + 1) + M.c_map +
        M.c_map * (8 + 1) * 2 * 4 + M.c_map + 4 <=
        256 * (M.c_map + 1) * (M.c_map + 1))%N).
    { pose proof (N.le_0_l M.c_map) as Hmap. clear -Hmap. nia. }
    pose proof (N.mul_le_mono_r _ _ work Hcoefficient) as Hbudget.
    repeat rewrite N.mul_add_distr_r in Hbudget.
    destruct (M.get target next) as [row|] eqn:Hrow.
    - assert (Hdata : code_work
        (fun z => (Z.size_nat d + Z.size_nat z + 1)%nat) row + 1 <= 4 * units).
      { unfold units. apply shift_selected_row_work_linear. exact Hrow. }
      pose proof (time_of_nat_le _ _ Hdata) as HdataN.
      rewrite (Nat2N.inj_mul 4 units) in HdataN. fold work in HdataN.
      pose proof (T_merge_left_code_work Z Z Z (shift_bound d)
        (fun a b => T_shift_bound d a b)
        (fun z => (Z.size_nat d + Z.size_nat z + 1)%nat)
        row 8%N (T_shift_bound_le d)) as Hmerge.
      assert (Hmerge_work : (M.T_merge (shift_bound d)
        (fun a b => T_shift_bound d a b) row M.empty <=
        M.c_map * (8 + 1) * 2 * (4 * work))%N).
      { eapply N.le_trans; [exact Hmerge|].
        apply N.mul_le_mono_l. exact HdataN. }
      assert (Hset : (M.T_set target
        (M.merge (shift_bound d) row M.empty) next <= M.c_map * work)%N).
      { eapply N.le_trans; [apply M.T_set_le|].
        apply N.mul_le_mono_l. exact HkeyN. }
      replace (M.c_map * (8 + 1) * 2 * (4 * work))%N with
        ((M.c_map * (8 + 1) * 2 * 4) * work)%N in Hmerge_work by ring.
      unfold T_shift_literal. cbn beta iota zeta. fold next. rewrite Hrow.
      cbn beta iota zeta. time_simpl.
      clearbody work. clear - Hcolumns Hget Hset Hmerge_work Hbudget Hwork. lia.
    - unfold T_shift_literal. cbn beta iota zeta. fold next. rewrite Hrow.
      cbn beta iota zeta. time_simpl.
      clearbody work. clear - Hcolumns Hget Hbudget Hwork. lia.
  Qed.

  (** Both signed literal translations have linear support cost. *)
  Lemma T_shift_linear : forall x d m,
    (T_shift x d m <= 2048 * (M.c_map + 1) * (M.c_map + 1) *
      N.of_nat ((supp m + 1) *
        (b m + ell m + X.bits x + Z.size_nat d + 1)))%N.
  Proof.
    intros x d m.
    set (units := (supp m + 1) *
      (b m + ell m + X.bits x + Z.size_nat d + 1)).
    set (work := N.of_nat units).
    assert (Hpositive : 1 <= units).
    { unfold units. eapply Nat.le_trans; [|apply linear_payload_le]. lia. }
    pose proof (time_of_nat_le _ _ Hpositive) as Hwork.
    change (1 <= work)%N in Hwork.
    assert (Hfirst_nat : (supp m + 1) *
      (b m + ell m + K.bits (x, true) + Z.size_nat d + 1) <= 2 * units).
    { unfold units. rewrite literal_bits. cbn beta iota zeta.
      replace (2 * ((supp m + 1) *
        (b m + ell m + X.bits x + Z.size_nat d + 1))) with
        ((supp m + 1) * (2 * (b m + ell m + X.bits x + Z.size_nat d + 1))) by ring.
      apply Nat.mul_le_mono_l. lia. }
    assert (Hfirst : (T_shift_literal (x, true) d m <=
      512 * (M.c_map + 1) * (M.c_map + 1) * work)%N).
    { eapply N.le_trans; [apply T_shift_literal_linear|].
      replace (512 * (M.c_map + 1) * (M.c_map + 1) * work)%N with
        (256 * (M.c_map + 1) * (M.c_map + 1) * (2 * work))%N by ring.
      apply N.mul_le_mono_l.
      pose proof (time_of_nat_le _ _ Hfirst_nat) as Hcast.
      rewrite (Nat2N.inj_mul 2 units) in Hcast. exact Hcast. }
    set (first := shift_literal (x, true) d m).
    destruct (shift_literal_sizes (x, true) d m) as [Hcount Hkeys].
    pose proof (ell_shift_literal (x, true) d m) as Hell.
    fold first in Hcount, Hkeys, Hell.
    assert (Hsecond_nat : (supp first + 1) *
      (b first + ell first + K.bits (x, false) + Z.size_nat (-d)%Z + 1) <= 3 * units).
    { unfold units. rewrite Hcount, Hkeys, literal_bits, zbits_opp.
      cbn beta iota zeta.
      replace (3 * ((supp m + 1) *
        (b m + ell m + X.bits x + Z.size_nat d + 1))) with
        ((supp m + 1) * (3 * (b m + ell m + X.bits x + Z.size_nat d + 1))) by ring.
      apply Nat.mul_le_mono_l. lia. }
    assert (Hsecond : (T_shift_literal (x, false) (-d)%Z first <=
      768 * (M.c_map + 1) * (M.c_map + 1) * work)%N).
    { eapply N.le_trans; [apply T_shift_literal_linear|].
      replace (768 * (M.c_map + 1) * (M.c_map + 1) * work)%N with
        (256 * (M.c_map + 1) * (M.c_map + 1) * (3 * work))%N by ring.
      apply N.mul_le_mono_l.
      pose proof (time_of_nat_le _ _ Hsecond_nat) as Hcast.
      rewrite (Nat2N.inj_mul 3 units) in Hcast. exact Hcast. }
    pose proof (Z.T_opp_le d) as Hopp.
    assert (Hcoefficient :
      (512 * (M.c_map + 1) * (M.c_map + 1) +
        768 * (M.c_map + 1) * (M.c_map + 1) + 2 <=
        2048 * (M.c_map + 1) * (M.c_map + 1))%N).
    { pose proof (N.le_0_l M.c_map) as Hmap. clear -Hmap. nia. }
    pose proof (N.mul_le_mono_r _ _ work Hcoefficient) as Hbudget.
    repeat rewrite N.mul_add_distr_r in Hbudget.
    match goal with
    | |- N.le ?clock _ =>
      change (clock <= 2048 * (M.c_map + 1) * (M.c_map + 1) * work)%N
    end.
    unfold T_shift. cbn beta iota zeta. fold first. time_simpl.
    clearbody work. clear - Hfirst Hsecond Hopp Hbudget Hwork. lia.
  Qed.

  (** Setting or removing an optional bound charges only its target key. *)
  Lemma T_put_bound_le : forall target bound row,
    (T_put_bound target bound row <=
      8 * (M.c_map + 1) * N.of_nat (K.bits target + 1))%N.
  Proof.
    intros target [d|] row; time_step.
  Qed.

  (** A column copy reads one source entry and replaces one target entry. *)
  Definition copy_column_work (target source : K.t) (d : Z) (row : M.t Z) : nat :=
    K.bits target + K.bits source + Z.size_nat d +
      option_weight Z.size_nat (M.get source row) + 1.

  Lemma T_copy_column_row_le : forall target source d old ignored,
    (T_copy_column_row target source d old ignored <= 32 * (M.c_map + 1) *
      N.of_nat (option_weight (copy_column_work target source d) old + 1))%N.
  Proof.
    intros target source d [row|] ignored.
    - pose proof (M.T_get_le Z source row) as Hget.
      pose proof (T_edge_prefix_le d (M.get source row)) as Hprefix.
      pose proof (T_put_bound_le target (edge_prefix d (M.get source row)) row) as Hput.
      cbn [option_weight]. unfold copy_column_work, optional_bits in *.
      unfold T_copy_column_row. time_simpl. rewrite ?Nat2N.inj_add in *. nia.
    - unfold T_copy_column_row. time_simpl. cbn [option_weight]. nia.
  Qed.

  (** The column pass charges each row's source entry only once. *)
  Lemma copy_column_work_linear : forall target source d m,
    code_work (copy_column_work target source d) m + 1 <=
      3 * ((supp m + 1) *
        (b m + ell m + K.bits target + K.bits source + Z.size_nat d + 1)).
  Proof.
    intros target source d m.
    assert (Hsupport : forall p, In p (M.codes m) -> In p (support m)).
    { intros p Hp. apply support_spec. now left. }
    pose proof (nodes_support (M.t Z) m m Hsupport) as Hnodes.
    pose proof (codes_support_length (M.t Z) m m Hsupport) as Hcount.
    assert (Hstored : stored_weight (copy_column_work target source d) m <=
      length (M.codes m) * (K.bits target + K.bits source + Z.size_nat d + ell m + 1)).
    { apply stored_weight_uniform. intros p row Hrow. unfold copy_column_work.
      destruct (M.get source row) as [old|] eqn:Hentry; cbn [option_weight].
      - pose proof (row_get_bits m p row source old Hrow Hentry). lia.
      - lia. }
    unfold code_work. nia.
  Qed.

  (** The column-copy merge has linear support cost. *)
  Lemma T_copy_columns_linear : forall target source d m,
    (M.T_merge (copy_column_row target source d)
      (fun old ignored => T_copy_column_row target source d old ignored) m M.empty <=
      256 * (M.c_map + 1) * (M.c_map + 1) *
        N.of_nat ((supp m + 1) *
          (b m + ell m + K.bits target + K.bits source + Z.size_nat d + 1)))%N.
  Proof.
    intros target source d m.
    pose proof (T_merge_left_code_work (M.t Z) (M.t Z) (M.t Z)
      (copy_column_row target source d)
      (fun old ignored => T_copy_column_row target source d old ignored)
      (copy_column_work target source d) m (32 * (M.c_map + 1))%N
      (T_copy_column_row_le target source d)) as Hmerge.
    pose proof (time_of_nat_le _ _ (copy_column_work_linear target source d m)) as Hdata.
    rewrite Nat2N.inj_mul in Hdata.
    eapply N.le_trans; [exact Hmerge|].
    eapply N.le_trans; [apply N.mul_le_mono_l; exact Hdata|].
    rewrite N.mul_assoc. apply N.mul_le_mono_r. nia.
  Qed.

  (** The selected copied row has at most one extra literal's support work. *)
  Lemma copied_row_work_linear : forall target source d m,
    code_work (fun z => (Z.size_nat d + Z.size_nat z + 1)%nat)
      (row_of (M.get source (copy_column_matrix target source d m))) + 1 <=
      24 * ((supp m + 1) *
        (b m + ell m + K.bits target + K.bits source + Z.size_nat d + 1)).
  Proof.
    intros target source d m.
    set (next := copy_column_matrix target source d m).
    pose proof (code_work_bits_bound next (row_of (M.get source next))
      (Z.size_nat d) (ell next) (row_lookup_support next source)
      (row_lookup_bits next source)) as Hrow.
    destruct (copy_column_matrix_sizes target source d m) as [Hcount Hkeys].
    pose proof (ell_copy_column_matrix target source d m) as Hell.
    fold next in Hcount, Hkeys, Hell. nia.
  Qed.

  (** A literal copy performs one column pass and one shifted source-row pass. *)
  Lemma T_copy_literal_linear : forall target source d m,
    (T_copy_literal target source d m <= 1024 * (M.c_map + 1) * (M.c_map + 1) *
      N.of_nat ((supp m + 1) *
        (b m + ell m + K.bits target + K.bits source + Z.size_nat d + 1)))%N.
  Proof.
    intros target source d m.
    set (units := (supp m + 1) *
      (b m + ell m + K.bits target + K.bits source + Z.size_nat d + 1)).
    set (work := N.of_nat units).
    assert (Hpositive : (1 <= work)%N) by (unfold work, units; nia).
    assert (Htarget : (N.of_nat (K.bits target + 1) <= work)%N).
    { unfold work, units. apply time_of_nat_le. nia. }
    assert (Hsource : (N.of_nat (K.bits source + 1) <= work)%N).
    { unfold work, units. apply time_of_nat_le. nia. }
    pose proof (T_copy_columns_linear target source d m) as Hcolumns.
    fold units work in Hcolumns.
    set (next := copy_column_matrix target source d m).
    set (row := row_of (M.get source next)).
    pose proof (T_merge_left_code_work Z Z Z (shift_bound d)
      (fun a b => T_shift_bound d a b)
      (fun z => (Z.size_nat d + Z.size_nat z + 1)%nat) row 8%N
      (T_shift_bound_le d)) as Hrow.
    pose proof (time_of_nat_le _ _ (copied_row_work_linear target source d m)) as Hdata.
    fold next row units in Hdata. rewrite Nat2N.inj_mul in Hdata. fold work in Hdata.
    assert (Hmerge : (M.T_merge (shift_bound d) (fun a b => T_shift_bound d a b)
      row M.empty <= 432 * M.c_map * work)%N).
    { eapply N.le_trans; [exact Hrow|].
      eapply N.le_trans; [apply N.mul_le_mono_l; exact Hdata|].
      cbn [N.of_nat]. ring_simplify. apply N.le_refl. }
    assert (Hget : (M.T_get source next <= M.c_map * work)%N).
    { eapply N.le_trans; [apply M.T_get_le|]. now apply N.mul_le_mono_l. }
    assert (Hset : (M.T_set target (M.merge (shift_bound d) row M.empty) next <=
      M.c_map * work)%N).
    { eapply N.le_trans; [apply M.T_set_le|]. now apply N.mul_le_mono_l. }
    pose proof (T_row_of_le (M.get source next)) as Hrow_of.
    assert (Hcoefficient : (256 * (M.c_map + 1) * (M.c_map + 1) +
      434 * M.c_map + 4 <= 1024 * (M.c_map + 1) * (M.c_map + 1))%N) by (clear; nia).
    pose proof (N.mul_le_mono_r _ _ work Hcoefficient) as Hbudget.
    rewrite !N.mul_add_distr_r in Hbudget.
    change (T_copy_literal target source d m <=
      1024 * (M.c_map + 1) * (M.c_map + 1) * work)%N.
    unfold T_copy_literal. time_simpl. fold copy_column_matrix. fold next row.
    subst row next. unfold copy_column_matrix in *.
    clearbody work. clear - Hpositive Hcolumns Hmerge Hget Hset Hrow_of Hbudget. lia.
  Qed.

  (** Copying both signs has linear support cost and fixed offset growth. *)
  Lemma T_copy_literals_linear : forall x source d m,
    (T_copy_literals x source d m <= 65536 * (M.c_map + 1) * (M.c_map + 1) *
      N.of_nat ((supp m + 1) *
        (b m + ell m + X.bits x + K.bits source + Z.size_nat d + 1)))%N.
  Proof.
    intros x source d m.
    set (units := (supp m + 1) *
      (b m + ell m + X.bits x + K.bits source + Z.size_nat d + 1)).
    set (work := N.of_nat units).
    assert (Hpositive : (1 <= work)%N) by (unfold work, units; nia).
    assert (Hfirst_data : (supp m + 1) *
      (b m + ell m + K.bits (x, true) + K.bits source + Z.size_nat d + 1) <= 2 * units).
    { unfold units. rewrite literal_bits. cbn beta iota zeta. nia. }
    pose proof (T_copy_literal_linear (x, true) source d m) as Hfirst.
    pose proof (time_of_nat_le _ _ Hfirst_data) as Hfirst_cast.
    rewrite (Nat2N.inj_mul 2 units) in Hfirst_cast. fold work in Hfirst_cast.
    assert (Hfirst_time : (T_copy_literal (x, true) source d m <=
      2048 * (M.c_map + 1) * (M.c_map + 1) * work)%N).
    { eapply N.le_trans; [exact Hfirst|].
      eapply N.le_trans; [apply N.mul_le_mono_l; exact Hfirst_cast|].
      cbn [N.of_nat]. ring_simplify. apply N.le_refl. }
    set (first := copy_literal (x, true) source d m).
    destruct (copy_literal_sizes (x, true) source d m) as [Hcount Hkeys].
    pose proof (ell_copy_literal (x, true) source d m) as Hell.
    fold first in Hcount, Hkeys, Hell.
    assert (Hsecond_data : (supp first + 1) *
      (b first + ell first + K.bits (x, false) + K.bits (flip source) +
        Z.size_nat (-d)%Z + 1) <= 30 * units).
    { rewrite literal_bits, zbits_opp. cbn beta iota zeta.
      rewrite literal_bits in Hkeys. cbn beta iota zeta in Hkeys.
      pose proof (flip_bits source) as Hflip_bits.
      assert (Hsupport : supp first + 1 <= 5 * (supp m + 1)) by lia.
      assert (Hpayload : b first + ell first + (2 * X.bits x + 0) +
        K.bits (flip source) + Z.size_nat d + 1 <=
        6 * (b m + ell m + X.bits x + K.bits source + Z.size_nat d + 1)) by lia.
      unfold units. eapply Nat.le_trans.
      - apply Nat.mul_le_mono; [exact Hsupport|exact Hpayload].
      - ring_simplify. apply Nat.le_refl. }
    pose proof (T_copy_literal_linear (x, false) (flip source) (-d)%Z first) as Hsecond.
    pose proof (time_of_nat_le _ _ Hsecond_data) as Hsecond_cast.
    rewrite (Nat2N.inj_mul 30 units) in Hsecond_cast. fold work in Hsecond_cast.
    assert (Hsecond_time : (T_copy_literal (x, false) (flip source) (-d)%Z first <=
      30720 * (M.c_map + 1) * (M.c_map + 1) * work)%N).
    { eapply N.le_trans; [exact Hsecond|].
      eapply N.le_trans; [apply N.mul_le_mono_l; exact Hsecond_cast|].
      cbn [N.of_nat]. ring_simplify. apply N.le_refl. }
    pose proof (T_flip_le source) as Hflip. pose proof (Z.T_opp_le d) as Hopp.
    assert (Hcoefficient : (2048 * (M.c_map + 1) * (M.c_map + 1) +
      30720 * (M.c_map + 1) * (M.c_map + 1) + 6 <=
      65536 * (M.c_map + 1) * (M.c_map + 1))%N) by (clear; nia).
    pose proof (N.mul_le_mono_r _ _ work Hcoefficient) as Hbudget.
    rewrite !N.mul_add_distr_r in Hbudget.
    change (T_copy_literals x source d m <=
      65536 * (M.c_map + 1) * (M.c_map + 1) * work)%N.
    unfold T_copy_literals. time_simpl. fold first.
    clearbody work. clear - Hfirst_time Hsecond_time Hflip Hopp Hpositive Hbudget. lia.
  Qed.

  (** Materializing the source diagonals adds only its two signed codes. *)
  Lemma copy_seed_resources : forall source m,
    let seed := add_cons source source 0%Z m in
    supp seed <= supp m + 4 /\
    b seed <= b m + K.bits source + 1 /\ ell seed <= ell m.
  Proof.
    intros source m. cbn beta iota zeta.
    assert (Hsupport : forall p, In p (support (add_cons source source 0%Z m)) ->
      p = K.encode source \/ p = K.encode source \/ p = K.encode (flip source) \/
        p = K.encode (flip source) \/ In p (support m)).
    { intros p Hp. now apply support_add_cons in Hp. }
    destruct (support_signed_endpoints source source _ m Hsupport) as [Hcount Hbits].
    split; [exact Hcount|]. split.
    - rewrite Nat.max_id in Hbits. eapply Nat.le_trans; [exact Hbits|].
      apply Nat.max_lub; lia.
    - apply ell_add_cons; [lia|change (0 <= ell m); lia].
  Qed.

  (** Copy assignment has linear support cost, including source-diagonal materialization. *)
  Lemma T_assign_copy_fast_small : forall x source d s,
    (T_assign_copy_fast x source d s <=
      (1024 * 1024) * (M.c_map + K.c_key + 1) * (M.c_map + K.c_key + 1) *
      N.of_nat ((ns s + 1) *
        (bs s + ells s + X.bits x + K.bits source + Z.size_nat d + 1)))%N.
  Proof.
    intros x source d [|m].
    - unfold T_assign_copy_fast. time_simpl. cbn [ns bs ells].
      assert (Hpositive : (1 <= N.of_nat (X.bits x + K.bits source + Z.size_nat d + 1))%N)
        by lia.
      rewrite Nat.mul_1_l. nia.
    - cbn [ns bs ells].
      set (units := (supp m + 1) *
        (b m + ell m + X.bits x + K.bits source + Z.size_nat d + 1)).
      set (work := N.of_nat units).
      assert (Hpositive : (1 <= work)%N) by (unfold work, units; nia).
      assert (Hsource : (N.of_nat (K.bits source + 1) <= work)%N).
      { unfold work, units. apply time_of_nat_le. nia. }
      assert (Hequal : (K.T_eqb source (x, true) <= K.c_key * work)%N).
      { eapply N.le_trans; [apply K.T_eqb_le|]. now apply N.mul_le_mono_l. }
      assert (Hshift : (T_shift x d m <=
        2048 * (M.c_map + 1) * (M.c_map + 1) * work)%N).
      { eapply N.le_trans; [apply T_shift_linear|].
        apply N.mul_le_mono_l. unfold work, units. apply time_of_nat_le.
        apply Nat.mul_le_mono_l. lia. }
      set (seed := add_cons source source 0%Z m).
      destruct (copy_seed_resources source m) as [Hcount [Hkeys Hell]].
      fold seed in Hcount, Hkeys, Hell.
      assert (Hdata : (supp seed + 1) *
        (b seed + ell seed + X.bits x + K.bits source + Z.size_nat d + 1) <= 10 * units).
      { assert (Hsupport : supp seed + 1 <= 5 * (supp m + 1)) by lia.
        assert (Hpayload : b seed + ell seed + X.bits x + K.bits source +
          Z.size_nat d + 1 <=
          2 * (b m + ell m + X.bits x + K.bits source + Z.size_nat d + 1)) by lia.
        unfold units. eapply Nat.le_trans.
        - apply Nat.mul_le_mono; [exact Hsupport|exact Hpayload].
        - ring_simplify. apply Nat.le_refl. }
      pose proof (time_of_nat_le _ _ Hdata) as Hcast.
      rewrite (Nat2N.inj_mul 10 units) in Hcast. fold work in Hcast.
      pose proof (T_copy_literals_linear x source d seed) as Hcopies.
      assert (Hcopy_time : (T_copy_literals x source d seed <=
        655360 * (M.c_map + 1) * (M.c_map + 1) * work)%N).
      { eapply N.le_trans; [exact Hcopies|].
        eapply N.le_trans; [apply N.mul_le_mono_l; exact Hcast|].
        cbn [N.of_nat]. ring_simplify. apply N.le_refl. }
      assert (Hseed : (T_add_cons source source 0%Z m <= 512 * (M.c_map + 1) * work)%N).
      { eapply N.le_trans; [apply T_add_cons_small|].
        replace (512 * (M.c_map + 1) * work)%N with
          (256 * (M.c_map + 1) * (2 * work))%N by ring.
        apply N.mul_le_mono_l. unfold work, units. cbn [Z.size_nat].
        change 2%N with (N.of_nat 2).
        rewrite <- Nat2N.inj_mul. apply time_of_nat_le. clear; nia. }
      assert (Hcoefficient : (K.c_key +
        2048 * (M.c_map + 1) * (M.c_map + 1) +
        655360 * (M.c_map + 1) * (M.c_map + 1) + 512 * (M.c_map + 1) + 4 <=
        (1024 * 1024) * (M.c_map + K.c_key + 1) * (M.c_map + K.c_key + 1))%N) by (clear; nia).
      pose proof (N.mul_le_mono_r _ _ work Hcoefficient) as Hbudget.
      rewrite !N.mul_add_distr_r in Hbudget.
      change (T_assign_copy_fast x source d (Reached m) <=
        (1024 * 1024) * (M.c_map + K.c_key + 1) * (M.c_map + K.c_key + 1) * work)%N.
      unfold T_assign_copy_fast. time_simpl. fold seed.
      clearbody work. clear - Hpositive Hequal Hshift Hcopy_time Hseed Hbudget.
      destruct (K.eqb source (x, true)); time_simpl; lia.
  Qed.

  Lemma T_signed_unit_le : forall x a,
    (T_signed_unit x a <= 16 * N.of_nat (Z.size_nat a + 1))%N.
  Proof. intros x a. time_step. Qed.

(** A recognized signed copy names a variable already charged by its source form. *)
  Lemma copy_source_form_bits : forall f source, copy_source f = Some source ->
    X.bits (fst source) <= F.form_bits f.
  Proof.
    intros f source Hsource. unfold copy_source in Hsource.
    destruct (coef f) as [|[x a] cs] eqn:Hcoef; [discriminate|].
    destruct cs as [|p cs]; [|discriminate].
    assert (Hin : In (x, a) (coef f)) by (rewrite Hcoef; now left).
    pose proof (form_bits_key f (x, a) Hin) as Hbits. cbn [fst] in Hbits.
    unfold signed_unit in Hsource.
    destruct (a =? 1)%Z; [injection Hsource as <-; cbn [fst]; exact Hbits|].
    destruct (a =? -1)%Z; [injection Hsource as <-; cbn [fst]; exact Hbits|discriminate].
  Qed.

  Lemma copy_source_key_bits : forall f source, copy_source f = Some source ->
    K.bits source <= 2 * F.form_bits f + 1.
  Proof.
    intros f [x sign] Hsource.
    pose proof (copy_source_form_bits f (x, sign) Hsource) as Hbits.
    pose proof (signed_bits_le x sign) as Hsigned. cbn [fst] in Hbits. lia.
  Qed.

  (** Copy recognition inspects one coefficient and rejects longer forms immediately. *)
  Lemma T_copy_source_le : forall f,
    (T_copy_source f <= 32 * N.of_nat (F.form_bits f + 1))%N.
  Proof.
    intros [cs c]. destruct cs as [|[x a] cs].
    - time_step.
    - destruct cs as [|p cs].
      + pose proof (form_bits_coefficient (Lin X.t ((x, a) :: nil) c) (x, a)
          ltac:(cbn [coef]; now left)) as Hbits.
        cbn [snd] in Hbits. pose proof (T_signed_unit_le x a) as Hunit.
        time_step.
      + time_step.
  Qed.

  Lemma T_copy_allowed_le : forall x source,
    (T_copy_allowed x source <= 8 * (X.c_key + 1) *
      N.of_nat (X.bits (fst source) + 1))%N.
  Proof.
    intros x [y sign].
    pose proof (X.T_eqb_le y x) as Heq.
    unfold T_copy_allowed. time_simpl. cbn [fst snd] in *.
    destruct (X.eqb y x); time_simpl; rewrite ?Nat2N.inj_add in *; nia.
  Qed.

  (** State refinement inherits the signed incremental support, bit and label bounds. *)
  Lemma grow_refine : forall i j d s,
    ns (refine i j d s) <= ns s + 4 /\
    bs (refine i j d s) <= Nat.max (bs s) (Nat.max (K.bits i) (K.bits j) + 1) /\
    ells (refine i j d s) <= Nat.max (ells s) (Z.size_nat d) + 4 /\
    labs (refine i j d s) <= labs s + 4 * (Nat.max (K.bits i) (K.bits j) + 2).
  Proof.
    intros i j d [|m]; [cbn [refine ns bs ells labs]; repeat split; lia|].
    unfold refine. destruct (incr_close i j d m) as [|next] eqn:Hnext.
    - cbn [ns bs ells labs]. repeat split; lia.
    - cbn [ns bs ells labs]. exact (grow_incr_close i j d m next Hnext).
  Qed.

  (** Refinement adds state dispatch to the signed incremental matrix and label clock. *)
  Lemma T_refine_small : forall i j d s,
    (T_refine i j d s <= 1 + c_octagon * N.of_nat
      ((ns s + 1)^2 * (bs s + K.bits i + K.bits j + ells s + Z.size_nat d + 1) +
        labs s))%N.
  Proof.
    intros i j d [|m].
    - change (1 <= 1 + c_octagon * N.of_nat
        ((0 + 1)^2 * (0 + K.bits i + K.bits j + 0 + Z.size_nat d + 1) + 0))%N. lia.
    - change (1 + T_incr_close i j d m <= 1 + c_octagon * N.of_nat
        ((supp m + 1)^2 * (b m + K.bits i + K.bits j + ell m + Z.size_nat d + 1) +
          M.weight m))%N.
      replace (c_octagon * N.of_nat ((supp m + 1)^2 *
        (b m + K.bits i + K.bits j + ell m + Z.size_nat d + 1) + M.weight m))%N with
        (c_octagon * N.of_nat ((supp m + 1)^2) *
          N.of_nat (b m + K.bits i + K.bits j + ell m + Z.size_nat d + 1) +
          c_octagon * N.of_nat (M.weight m))%N
        by (rewrite (Nat2N.inj_add
          ((supp m + 1)^2 * (b m + K.bits i + K.bits j + ell m + Z.size_nat d + 1))
          (M.weight m)),
          (Nat2N.inj_mul ((supp m + 1)^2)
            (b m + K.bits i + K.bits j + ell m + Z.size_nat d + 1)); ring).
      apply N.add_le_mono_l, T_incr_close_le.
  Qed.

  (** Two opposite signed refinements share a quadratic matrix and label allowance. *)
  Lemma T_refine_pair_small : forall i j a b s bits,
    Z.size_nat a <= bits -> Z.size_nat b <= bits ->
    (T_refine i j a s + T_refine j i b (refine i j a s) <=
      256 * c_octagon * N.of_nat
        ((ns s + 1)^2 * (bs s + ells s + K.bits i + K.bits j + bits + 1) + labs s))%N.
  Proof.
    intros i j a b s bits Ha Hb.
    set (payload := bs s + ells s + K.bits i + K.bits j + bits + 1).
    set (matrix_units := (ns s + 1)^2 * payload).
    set (units := matrix_units + labs s).
    assert (Hfirst_work : (ns s + 1)^2 *
      (bs s + K.bits i + K.bits j + ells s + Z.size_nat a + 1) + labs s <= units).
    { unfold units, matrix_units. apply Nat.add_le_mono_r, Nat.mul_le_mono_l.
      unfold payload. lia. }
    pose proof (time_of_nat_le _ _ Hfirst_work) as Hfirst_cast.
    assert (Hfirst : (T_refine i j a s <= 1 + c_octagon * N.of_nat units)%N).
    { eapply N.le_trans; [apply T_refine_small|].
      apply N.add_le_mono_l, N.mul_le_mono_l. exact Hfirst_cast. }
    set (next := refine i j a s).
    destruct (grow_refine i j a s) as [Hcount [Hbits [Hell Hlabels]]].
    fold next in Hcount, Hbits, Hell, Hlabels.
    assert (Hkey_sum : Nat.max (K.bits i) (K.bits j) <= K.bits i + K.bits j).
    { apply Nat.max_lub; lia. }
    assert (Hkey_cap : Nat.max (bs s) (Nat.max (K.bits i) (K.bits j) + 1) <=
      bs s + K.bits i + K.bits j + 1).
    { apply Nat.max_lub; lia. }
    assert (Hentry_cap : Nat.max (ells s) (Z.size_nat a) <= ells s + bits).
    { apply Nat.max_lub; lia. }
    assert (Hsquare : (ns next + 1)^2 <= 25 * (ns s + 1)^2).
    { clear -Hcount. cbn [Nat.pow]. nia. }
    assert (Hpayload : bs next + K.bits j + K.bits i + ells next + Z.size_nat b + 1 <=
      6 * payload).
    { unfold payload. lia. }
    assert (Hsecond_matrix : (ns next + 1)^2 *
      (bs next + K.bits j + K.bits i + ells next + Z.size_nat b + 1) <=
      150 * matrix_units).
    { replace (150 * matrix_units) with
        ((25 * (ns s + 1)^2) * (6 * payload)) by (unfold matrix_units; ring).
      now apply Nat.mul_le_mono. }
    assert (Hlabel_work : labs next <= labs s + 8 * payload).
    { unfold payload. lia. }
    assert (Hquadratic : payload <= matrix_units).
    { unfold matrix_units. replace payload with (1 * payload) at 1 by ring.
      apply Nat.mul_le_mono_r. clear -s. cbn [Nat.pow]. nia. }
    assert (Hsecond_work : (ns next + 1)^2 *
      (bs next + K.bits j + K.bits i + ells next + Z.size_nat b + 1) + labs next <=
      160 * units).
    { clear -Hsecond_matrix Hlabel_work Hquadratic units. unfold units. lia. }
    pose proof (time_of_nat_le _ _ Hsecond_work) as Hsecond_cast.
    rewrite (Nat2N.inj_mul 160 units) in Hsecond_cast.
    assert (Hsecond : (T_refine j i b next <=
      1 + c_octagon * (160 * N.of_nat units))%N).
    { eapply N.le_trans; [apply T_refine_small|].
      apply N.add_le_mono_l, N.mul_le_mono_l. exact Hsecond_cast. }
    assert (Hunit : (1 <= N.of_nat units)%N).
    { change (N.of_nat 1%nat <= N.of_nat units)%N. apply time_of_nat_le.
      clear -units. unfold units, matrix_units, payload. cbn [Nat.pow]. nia. }
    assert (Hcoefficient : (1 <= c_octagon)%N).
    { pose proof (N.le_0_l M.c_map) as Hmap. clear -Hmap. unfold c_octagon. nia. }
    assert (Hpositive : (1 <= c_octagon * N.of_nat units)%N).
    { change (1 * 1 <= c_octagon * N.of_nat units)%N. now apply N.mul_le_mono. }
    fold next. fold payload. fold matrix_units. fold units.
    replace (c_octagon * (160 * N.of_nat units))%N with
      (160 * (c_octagon * N.of_nat units))%N in Hsecond by ring.
    replace (256 * c_octagon * N.of_nat units)%N with
      (256 * (c_octagon * N.of_nat units))%N by ring.
    set (charge := (c_octagon * N.of_nat units)%N) in *.
    clear -Hfirst Hsecond Hpositive. clearbody charge. lia.
  Qed.

  (** Doubling a finite endpoint adds at most one magnitude bit. *)
  Lemma zbits_twice : forall z, Z.size_nat (2 * z)%Z <= Z.size_nat z + 1.
  Proof.
    intro z. replace (2 * z)%Z with (z + z)%Z by ring.
    apply zbits_add_bound; apply Nat.le_refl.
  Qed.

  Lemma zbits_neg_twice : forall z, Z.size_nat (-2 * z)%Z <= Z.size_nat z + 1.
  Proof.
    intro z. replace (-2 * z)%Z with (-(2 * z))%Z by ring.
    rewrite zbits_opp. apply zbits_twice.
  Qed.

  (** Installing signed interval endpoints performs two bounded refinements and scalings. *)
  (** Averaging a finite bound charges only the present unary payload. *)
  Lemma T_range_average_le : forall bound unary ignored,
    (T_range_average bound unary ignored <= 32 * N.of_nat
      (option_weight (fun z => (option_weight Z.size_nat bound + Z.size_nat z + 1)%nat)
        unary + 1))%N.
  Proof.
    intros [a|] [z|] ignored; cbn [option_weight];
      try (pose proof (zbits_add_sum a z)); time_step.
  Qed.

  (** Updating two columns pays for two key writes and the present unary integer. *)
  Lemma T_range_column_row_le : forall x lower upper old unary,
    (T_range_column_row x lower upper old unary <= 128 * (M.c_map + 1) * N.of_nat
      (option_weight (fun _ : M.t Z => (X.bits x + option_weight Z.size_nat lower +
        option_weight Z.size_nat upper + 1)%nat) old +
        option_weight Z.size_nat unary + 1))%N.
  Proof.
    intros x lower upper [row|] unary; cbn [option_weight].
    - pose proof (T_range_average_le lower unary None) as Hlower.
      pose proof (T_range_average_le upper unary None) as Hupper.
      pose proof (T_put_bound_le (x, true) (range_average upper unary None) row) as Hputu.
      pose proof (T_put_bound_le (x, false) (range_average lower unary None)
        (put_bound (x, true) (range_average upper unary None) row)) as Hputl.
      rewrite !literal_bits in Hputu, Hputl. cbn beta iota zeta in Hputu, Hputl.
      destruct unary as [z|]; cbn [option_weight] in *;
        unfold T_range_column_row; time_simpl;
        rewrite ?Nat2N.inj_add, ?Nat2N.inj_mul in *; nia.
    - unfold T_range_column_row. time_simpl. nia.
  Qed.

  (** A new literal row traverses the unary map once and writes two signed entries. *)
  Lemma T_range_literal_row_le : forall x sign bound unaries,
    (T_range_literal_row x sign bound unaries <= 256 * (M.c_map + 1) * N.of_nat
      (X.bits x + code_work (fun z =>
        (option_weight Z.size_nat bound + Z.size_nat z + 1)%nat) unaries + 1))%N.
  Proof.
    intros x sign bound unaries.
    pose proof (T_merge_left_code_work Z Z Z (range_average bound)
      (fun unary ignored => T_range_average bound unary ignored)
      (fun z => (option_weight Z.size_nat bound + Z.size_nat z + 1)%nat)
      unaries 32%N (T_range_average_le bound)) as Hmerge.
    set (row := match bound with
      | Some _ => M.merge (range_average bound) unaries M.empty
      | None => M.empty
      end).
    pose proof (T_put_bound_le (x, negb sign) bound row) as Hput.
    pose proof (M.T_set_le Z (x, sign) 0%Z
      (put_bound (x, negb sign) bound row)) as Hset.
    set (work := N.of_nat (X.bits x + code_work (fun z =>
      (option_weight Z.size_nat bound + Z.size_nat z + 1)%nat) unaries + 1)).
    assert (Hpositive : (1 <= work)%N) by (unfold work; lia).
    assert (Hkey : forall s, (N.of_nat (K.bits (x, s) + 1) <= 2 * work)%N).
    { intro s. unfold work. rewrite literal_bits.
      destruct s; cbn beta iota zeta;
        rewrite !Nat2N.inj_add, ?Nat2N.inj_mul; lia. }
    assert (Hpayload : (N.of_nat (code_work (fun z =>
      (option_weight Z.size_nat bound + Z.size_nat z + 1)%nat) unaries + 1) <= work)%N).
    { unfold work. lia. }
    assert (Hput_work : (T_put_bound (x, negb sign) bound row <=
      16 * (M.c_map + 1) * work)%N).
    { eapply N.le_trans; [exact Hput|].
      replace (16 * (M.c_map + 1) * work)%N with
        (8 * (M.c_map + 1) * (2 * work))%N by ring.
      apply N.mul_le_mono_l. apply Hkey. }
    assert (Hset_work : (M.T_set (x, sign) 0%Z
      (put_bound (x, negb sign) bound row) <= 2 * M.c_map * work)%N).
    { eapply N.le_trans; [exact Hset|].
      replace (2 * M.c_map * work)%N with (M.c_map * (2 * work))%N by ring.
      apply N.mul_le_mono_l. apply Hkey. }
    assert (Hmerge_work : (M.T_merge (range_average bound)
      (fun unary ignored => T_range_average bound unary ignored) unaries M.empty <=
      66 * M.c_map * work)%N).
    { eapply N.le_trans; [exact Hmerge|].
      replace (66 * M.c_map * work)%N with (M.c_map * (32 + 1) * 2 * work)%N by ring.
      now apply N.mul_le_mono_l. }
    assert (Hcoefficient : (16 * (M.c_map + 1) + 2 * M.c_map + 66 * M.c_map + 2 <=
      256 * (M.c_map + 1))%N) by lia.
    pose proof (N.mul_le_mono_r _ _ work Hcoefficient) as Hbudget.
    rewrite !N.mul_add_distr_r in Hbudget.
    fold work. unfold T_range_literal_row. destruct bound as [a|]; fold row; time_simpl;
      clearbody work; clear - Hpositive Hput_work Hset_work Hmerge_work Hbudget; lia.
  Qed.

  (** Interval construction charges the raw labels and one supported row or column per literal. *)
  Definition range_matrix_work (x : X.t) (lower upper : option Z) (m : dbm) : nat :=
    (supp m + 1) * (b m + ell m + X.bits x + option_weight Z.size_nat lower +
      option_weight Z.size_nat upper + 1) + M.weight m.

  (** The outer merge visits only outer rows and the supported unary map. *)
  Lemma range_matrix_maps_work : forall x lower upper m,
    code_work (fun _ : M.t Z => (X.bits x + option_weight Z.size_nat lower +
      option_weight Z.size_nat upper + 1)%nat) m +
      code_work Z.size_nat (fst (M.fold (unary_maps m) m (M.empty, M.empty))) + 1 <=
    8 * range_matrix_work x lower upper m.
  Proof.
    intros x lower upper m.
    assert (Houter : forall p, In p (M.codes m) -> In p (support m)).
    { intros p Hp. apply support_spec. now left. }
    pose proof (nodes_support (M.t Z) m m Houter) as Hnodes.
    pose proof (codes_support_length (M.t Z) m m Houter) as Hcount.
    pose proof (stored_weight_uniform (M.t Z)
      (fun _ : M.t Z => (X.bits x + option_weight Z.size_nat lower +
        option_weight Z.size_nat upper + 1)%nat) m
      (X.bits x + option_weight Z.size_nat lower + option_weight Z.size_nat upper + 1)
      ltac:(intros p row Hrow; apply Nat.le_refl)) as Hstored.
    destruct (collect_unary_support m) as [Hsupport _].
    destruct (collect_unary_bits m) as [Hbits _].
    assert (Hunary : code_work Z.size_nat
      (fst (M.fold (unary_maps m) m (M.empty, M.empty))) <= supp m * (b m + ell m + 3)).
    { eapply Nat.le_trans with (code_work (fun z => (0 + Z.size_nat z + 1)%nat)
        (fst (M.fold (unary_maps m) m (M.empty, M.empty)))).
      - apply code_work_mono. intros p z Hz.
        lia.
      - eapply Nat.le_trans; [apply code_work_bits_bound; eassumption|].
        apply Nat.mul_le_mono_l. lia. }
    unfold code_work at 1. unfold range_matrix_work. nia.
  Qed.

  (** Either new literal row has linear work in the original support and endpoint bits. *)
  Lemma range_matrix_literal_work : forall x lower upper m bound,
    option_weight Z.size_nat bound <=
      option_weight Z.size_nat lower + option_weight Z.size_nat upper ->
    X.bits x + code_work (fun z =>
      (option_weight Z.size_nat bound + Z.size_nat z + 1)%nat)
      (snd (M.fold (unary_maps m) m (M.empty, M.empty))) + 1 <=
    4 * range_matrix_work x lower upper m.
  Proof.
    intros x lower upper m bound Hbound.
    destruct (collect_unary_support m) as [_ Hsupport].
    destruct (collect_unary_bits m) as [_ Hbits].
    pose proof (code_work_bits_bound m
      (snd (M.fold (unary_maps m) m (M.empty, M.empty)))
      (option_weight Z.size_nat bound) (ell m) Hsupport Hbits) as Hwork.
    unfold range_matrix_work. nia.
  Qed.

  (** Collecting the unary rows charges their labels without requiring consistent map labels. *)
  Lemma range_matrix_fold_time : forall x lower upper m,
    (M.T_fold (unary_maps m) (fun acc k row => T_unary_maps m acc k row)
      m (M.empty, M.empty) <= M.c_map * (64 * (M.c_map + 1) + 1) *
      N.of_nat (range_matrix_work x lower upper m))%N.
  Proof.
    intros x lower upper m.
    pose proof (T_fold_label_weight (M.t Z) (M.t Z * M.t Z)%type (unary_maps m)
      (fun acc k row => T_unary_maps m acc k row) m (M.empty, M.empty)
      (64 * (M.c_map + 1))%N (T_unary_maps_le m)) as Hfold.
    assert (Houter : forall p, In p (M.codes m) -> In p (support m)).
    { intros p Hp. apply support_spec. now left. }
    pose proof (nodes_support (M.t Z) m m Houter) as Hnodes.
    assert (Hnode : M.nodes m + 1 <= range_matrix_work x lower upper m).
    { unfold range_matrix_work. nia. }
    assert (Hlabels : M.weight m <= range_matrix_work x lower upper m).
    { unfold range_matrix_work. lia. }
    pose proof (time_of_nat_le _ _ Hnode) as HnodeN.
    pose proof (time_of_nat_le _ _ Hlabels) as HlabelN.
    eapply N.le_trans; [exact Hfold|].
    replace (M.c_map * (64 * (M.c_map + 1) + 1) *
      N.of_nat (range_matrix_work x lower upper m))%N with
      (M.c_map * ((64 * (M.c_map + 1) + 1) *
        N.of_nat (range_matrix_work x lower upper m)))%N by ring.
    apply N.mul_le_mono_l.
    rewrite N.mul_add_distr_r, N.mul_1_l.
    pose proof (N.mul_le_mono_l _ _ (64 * (M.c_map + 1))%N HlabelN). lia.
  Qed.

  (** Installing both interval literals takes linear support work and the raw label sum. *)
  Lemma T_range_matrix_le : forall x lower upper m,
    (T_range_matrix x lower upper m <= 8192 * (M.c_map + 1) * (M.c_map + 1) *
      N.of_nat (range_matrix_work x lower upper m))%N.
  Proof.
    intros x lower upper m.
    set (unaries := M.fold (unary_maps m) m (M.empty, M.empty)).
    set (next := M.merge (range_column_row x lower upper) m (fst unaries)).
    set (work := N.of_nat (range_matrix_work x lower upper m)).
    assert (Hpositive : (1 <= work)%N) by (unfold work, range_matrix_work; nia).
    pose proof (range_matrix_fold_time x lower upper m) as Hfold. fold work in Hfold.
    pose proof (T_merge_code_work (M.t Z) Z (M.t Z) (range_column_row x lower upper)
      (fun old unary => T_range_column_row x lower upper old unary)
      (fun _ : M.t Z => (X.bits x + option_weight Z.size_nat lower +
        option_weight Z.size_nat upper + 1)%nat) Z.size_nat m (fst unaries)
      (128 * (M.c_map + 1))%N (T_range_column_row_le x lower upper)) as Hmerge.
    pose proof (time_of_nat_le _ _ (range_matrix_maps_work x lower upper m)) as Hmaps.
    rewrite Nat2N.inj_mul in Hmaps. fold unaries work in Hmaps.
    assert (Hmerge_work : (M.T_merge (range_column_row x lower upper)
      (fun old unary => T_range_column_row x lower upper old unary) m (fst unaries) <=
      16 * M.c_map * (128 * (M.c_map + 1) + 1) * work)%N).
    { eapply N.le_trans; [exact Hmerge|].
      replace (16 * M.c_map * (128 * (M.c_map + 1) + 1) * work)%N with
        (M.c_map * (128 * (M.c_map + 1) + 1) * 2 * (8 * work))%N by ring.
      now apply N.mul_le_mono_l. }
    assert (Hrow : forall sign bound, option_weight Z.size_nat bound <=
        option_weight Z.size_nat lower + option_weight Z.size_nat upper ->
      (T_range_literal_row x sign bound (snd unaries) <= 1024 * (M.c_map + 1) * work)%N).
    { intros sign bound Hbound. eapply N.le_trans; [apply T_range_literal_row_le|].
      pose proof (time_of_nat_le _ _
        (range_matrix_literal_work x lower upper m bound Hbound)) as Hrowwork.
      rewrite Nat2N.inj_mul in Hrowwork. fold unaries work in Hrowwork.
      replace (1024 * (M.c_map + 1) * work)%N with
        (256 * (M.c_map + 1) * (4 * work))%N by ring.
      now apply N.mul_le_mono_l. }
    pose proof (Hrow true lower ltac:(lia)) as Hlower.
    pose proof (Hrow false upper ltac:(lia)) as Hupper.
    assert (Hset : forall sign (row : M.t Z) (base : dbm),
      (M.T_set (x, sign) row base <= 2 * M.c_map * work)%N).
    { intros sign row base. eapply N.le_trans; [apply M.T_set_le|].
      replace (2 * M.c_map * work)%N with (M.c_map * (2 * work))%N by ring.
      apply N.mul_le_mono_l.
      assert (Hkey : K.bits (x, sign) + 1 <= 2 * range_matrix_work x lower upper m).
      { rewrite literal_bits. unfold range_matrix_work. destruct sign; cbn beta iota zeta; nia. }
      pose proof (time_of_nat_le _ _ Hkey) as Hcast. rewrite Nat2N.inj_mul in Hcast.
      exact Hcast. }
    pose proof (Hset false (range_literal_row x false upper (snd unaries)) next) as Hsetu.
    pose proof (Hset true (range_literal_row x true lower (snd unaries))
      (M.set (x, false) (range_literal_row x false upper (snd unaries)) next)) as Hsetl.
    assert (Hcoefficient : (M.c_map * (64 * (M.c_map + 1) + 1) +
      16 * M.c_map * (128 * (M.c_map + 1) + 1) + 2 * (1024 * (M.c_map + 1)) +
      4 * M.c_map + 10 <= 8192 * (M.c_map + 1) * (M.c_map + 1))%N) by nia.
    pose proof (N.mul_le_mono_r _ _ work Hcoefficient) as Hbudget.
    rewrite !N.mul_add_distr_r in Hbudget.
    unfold T_range_matrix. time_simpl. fold unaries next.
    clearbody work. clear - Hfold Hmerge_work Hlower Hupper Hsetu Hsetl Hbudget Hpositive. lia.
  Qed.

  (** Finite, one-sided and crossed ranges all use the linear interval constructor. *)
  Lemma T_add_range_fast_small : forall x bounds s bits,
    rel_bounds_abs (2 ^ bits) bounds ->
    (T_add_range_fast x bounds s <= 512 * c_octagon * N.of_nat
      ((ns s + 1) * (bs s + ells s + 4 * X.bits x + bits + 3) + labs s))%N.
  Proof.
    intros x [lo hi] [|m] bits Hbounds.
    - unfold T_add_range_fast, c_octagon. cbn [ns bs ells labs]. time_simpl. nia.
    - set (units := (supp m + 1) * (b m + ell m + 4 * X.bits x + bits + 3) + M.weight m).
      set (charge := (c_octagon * N.of_nat units)%N).
      assert (Hcoefficient : (1 <= c_octagon)%N) by (unfold c_octagon; nia).
      assert (Hunit : (1 <= N.of_nat units)%N) by (unfold units; nia).
      assert (Hpositive : (1 <= charge)%N).
      { unfold charge. change (1 * 1 <= c_octagon * N.of_nat units)%N.
        now apply N.mul_le_mono. }
      assert (Hbits_work : bits + 1 <= units) by (unfold units; nia).
      assert (Hbits_charge : (N.of_nat (bits + 1) <= charge)%N).
      { unfold charge. eapply N.le_trans; [apply time_of_nat_le; exact Hbits_work|].
        replace (N.of_nat units) with (1 * N.of_nat units)%N at 1 by ring.
        now apply N.mul_le_mono_r. }
      assert (Hscale : forall c a, Z.size_nat c <= 2 -> Z.size_nat a <= bits ->
        (Z.T_mul c a <= 16 * charge)%N).
      { intros c a Hc Ha. eapply N.le_trans;
          [exact (rel_mul_small_time c a bits Hc Ha)|]. now apply N.mul_le_mono_l. }
      assert (Hcompare : forall a b, Z.size_nat a <= bits ->
        (Z.T_leb a b <= 4 * charge)%N).
      { intros a b Ha. pose proof (Z.T_leb_le a b) as Hclock.
        assert (Hsmall : (Z.T_leb a b <= 4 * N.of_nat (bits + 1))%N).
        { rewrite Nat2N.inj_add. lia. }
        eapply N.le_trans; [exact Hsmall|]. now apply N.mul_le_mono_l. }
      assert (Hmatrix : forall lower upper,
        option_weight Z.size_nat lower <= bits + 1 ->
        option_weight Z.size_nat upper <= bits + 1 ->
        (T_range_matrix x lower upper m <= charge)%N).
      { intros lower upper Hlower Hupper.
        assert (Hwork : range_matrix_work x lower upper m <= 2 * units).
        { unfold range_matrix_work, units. nia. }
        pose proof (time_of_nat_le _ _ Hwork) as Hcast.
        rewrite Nat2N.inj_mul in Hcast.
        eapply N.le_trans; [apply T_range_matrix_le|].
        eapply N.le_trans with
          (8192 * (M.c_map + 1) * (M.c_map + 1) * (2 * N.of_nat units))%N.
        - now apply N.mul_le_mono_l.
        - unfold charge, c_octagon. nia. }
      cbn [ns bs ells labs]. fold units.
      replace (512 * c_octagon * N.of_nat units)%N with (512 * charge)%N
        by (unfold charge; ring).
      clear Hcoefficient Hunit Hbits_work Hbits_charge.
      clearbody charge. clear units.
      destruct lo as [|lo|], hi as [|hi|];
        unfold rel_bounds_abs, rel_bound_abs in Hbounds;
        cbn [fst snd] in Hbounds; destruct Hbounds as [Hlo Hhi];
        try apply rel_zbits_least in Hlo; try apply rel_zbits_least in Hhi;
        try (pose proof (Hscale (-2)%Z lo ltac:(change (2 <= 2); lia) Hlo) as Hls);
        try (pose proof (Hscale 2%Z hi ltac:(change (2 <= 2); lia) Hhi) as Hus).
      all: try (pose proof (Hmatrix None (Some (2 * hi)%Z) ltac:(cbn [option_weight]; lia)
        ltac:(cbn [option_weight]; pose proof (zbits_twice hi); lia)) as Hupper).
      all: try (pose proof (Hmatrix (Some (-2 * lo)%Z) None
        ltac:(cbn [option_weight]; pose proof (zbits_neg_twice lo); lia)
        ltac:(cbn [option_weight]; lia)) as Hlower).
      all: try (pose proof (Hmatrix (Some (-2 * lo)%Z) (Some (2 * hi)%Z)
        ltac:(cbn [option_weight]; pose proof (zbits_neg_twice lo); lia)
        ltac:(cbn [option_weight]; pose proof (zbits_twice hi); lia)) as Hboth).
      all: try (pose proof (Hcompare lo hi Hlo) as Hcmp).
      all: unfold T_add_range_fast; time_simpl; try destruct (lo <=? hi)%Z; lia.
  Qed.

  Lemma T_add_range_small : forall x bounds s bits,
    rel_bounds_abs (2 ^ bits) bounds ->
    (T_add_range x bounds s <= 512 * c_octagon * N.of_nat
      ((ns s + 1)^2 * (bs s + ells s + 4 * X.bits x + bits + 3) + labs s))%N.
  Proof.
    intros x [lo hi] s bits Hbounds.
    set (units := (ns s + 1)^2 * (bs s + ells s + 4 * X.bits x + bits + 3) + labs s).
    set (charge := (c_octagon * N.of_nat units)%N).
    assert (Hcoefficient : (1 <= c_octagon)%N).
    { pose proof (N.le_0_l M.c_map) as Hmap. clear -Hmap. unfold c_octagon. nia. }
    assert (Hunit : (1 <= N.of_nat units)%N).
    { change (N.of_nat 1%nat <= N.of_nat units)%N. apply time_of_nat_le.
      clear -units. unfold units. cbn [Nat.pow]. nia. }
    assert (Hpositive : (1 <= charge)%N).
    { unfold charge. change (1 * 1 <= c_octagon * N.of_nat units)%N.
      now apply N.mul_le_mono. }
    assert (Hbits_work : bits + 1 <= units).
    { pose proof (quadratic_payload_le (ns s)
        (bs s + ells s + 4 * X.bits x + bits + 3)) as Hquadratic.
      unfold units. lia. }
    assert (Hbits_charge : (N.of_nat (bits + 1) <= charge)%N).
    { unfold charge. eapply N.le_trans; [exact (time_of_nat_le _ _ Hbits_work)|].
      replace (N.of_nat units) with (1 * N.of_nat units)%N at 1 by ring.
      now apply N.mul_le_mono_r. }
    assert (Hscale : forall c a, Z.size_nat c <= 2 -> Z.size_nat a <= bits ->
      (Z.T_mul c a <= 16 * charge)%N).
    { intros c a Hc Ha. eapply N.le_trans;
        [exact (rel_mul_small_time c a bits Hc Ha)|].
      now apply N.mul_le_mono_l. }
    assert (Hlower : forall a, Z.size_nat a <= bits ->
      (T_refine (x, true) (x, false) (-2 * a)%Z s <= 256 * charge)%N).
    { intros a Ha.
      pose proof (T_refine_pair_small (x, true) (x, false) (-2 * a)%Z 0%Z s (bits + 1)
        ltac:(pose proof (zbits_neg_twice a); lia) ltac:(cbn [Z.size_nat]; lia)) as Htime.
      rewrite !literal_bits in Htime. cbn beta iota zeta in Htime.
      replace (bs s + ells s + (2 * X.bits x + 1) + (2 * X.bits x + 0) +
        (bits + 1) + 1) with (bs s + ells s + 4 * X.bits x + bits + 3) in Htime by lia.
      fold units in Htime.
      replace (256 * c_octagon * N.of_nat units)%N with (256 * charge)%N in Htime
        by (unfold charge; ring).
      lia. }
    assert (Hupper : forall a, Z.size_nat a <= bits ->
      (T_refine (x, false) (x, true) (2 * a)%Z s <= 256 * charge)%N).
    { intros a Ha.
      pose proof (T_refine_pair_small (x, false) (x, true) (2 * a)%Z 0%Z s (bits + 1)
        ltac:(pose proof (zbits_twice a); lia) ltac:(cbn [Z.size_nat]; lia)) as Htime.
      rewrite !literal_bits in Htime. cbn beta iota zeta in Htime.
      replace (bs s + ells s + (2 * X.bits x + 0) + (2 * X.bits x + 1) +
        (bits + 1) + 1) with (bs s + ells s + 4 * X.bits x + bits + 3) in Htime by lia.
      fold units in Htime.
      replace (256 * c_octagon * N.of_nat units)%N with (256 * charge)%N in Htime
        by (unfold charge; ring).
      lia. }
    assert (Hboth : forall a b, Z.size_nat a <= bits -> Z.size_nat b <= bits ->
      (T_refine (x, true) (x, false) (-2 * a)%Z s +
        T_refine (x, false) (x, true) (2 * b)%Z
          (refine (x, true) (x, false) (-2 * a)%Z s) <= 256 * charge)%N).
    { intros a b Ha Hb.
      pose proof (T_refine_pair_small (x, true) (x, false) (-2 * a)%Z (2 * b)%Z s
        (bits + 1) ltac:(pose proof (zbits_neg_twice a); lia)
        ltac:(pose proof (zbits_twice b); lia)) as Htime.
      rewrite !literal_bits in Htime. cbn beta iota zeta in Htime.
      replace (bs s + ells s + (2 * X.bits x + 1) + (2 * X.bits x + 0) +
        (bits + 1) + 1) with (bs s + ells s + 4 * X.bits x + bits + 3) in Htime by lia.
      fold units in Htime.
      replace (256 * c_octagon * N.of_nat units)%N with (256 * charge)%N in Htime
        by (unfold charge; ring).
      exact Htime. }
    fold units. replace (512 * c_octagon * N.of_nat units)%N with (512 * charge)%N
      by (unfold charge; ring).
    clear Hcoefficient Hunit Hbits_work Hbits_charge.
    clearbody charge. clear units.
    destruct lo as [|lo|], hi as [|hi|];
      unfold rel_bounds_abs, rel_bound_abs in Hbounds;
      cbn [fst snd] in Hbounds; destruct Hbounds as [Hlo Hhi];
      try apply rel_zbits_least in Hlo; try apply rel_zbits_least in Hhi;
      try (pose proof (Hlower lo Hlo) as Hlower_time);
      try (pose proof (Hupper hi Hhi) as Hupper_time);
      try (pose proof (Hboth lo hi Hlo Hhi) as Hboth_time);
      try (pose proof (Hscale (-2)%Z lo ltac:(change (2 <= 2); lia) Hlo) as Hlower_scale);
      try (pose proof (Hscale 2%Z hi ltac:(change (2 <= 2); lia) Hhi) as Hupper_scale);
      time_unfold (@T_add_range); time_simpl; cbn beta iota zeta delta [fst snd]; lia.
  Qed.

  (** A source logarithm is paid by matrix key entropy or by the source-size term. *)
  Lemma support_log_work : forall m nodes,
    (supp m + 1)^2 * Nat.log2 nodes <=
      2 * ((supp m + 1)^2 * b m) +
        (nodes + 1) * (b m + Nat.log2 nodes + 1)^2.
  Proof.
    intros m nodes. destruct (Nat.le_gt_cases nodes ((supp m + 1)^2)) as [Hsmall|Hlarge].
    - assert (Hsquare : (supp m + 1)^2 <= 2 ^ (2 * b m)).
      { replace (2 * b m) with (b m + b m) by lia. rewrite Nat.pow_add_r.
        cbn [Nat.pow]. rewrite Nat.mul_1_r.
        apply Nat.mul_le_mono; apply support_cardinality_power. }
      assert (Hlog : Nat.log2 nodes <= 2 * b m).
      { pose proof (Nat.log2_le_mono nodes (2 ^ (2 * b m))
          (Nat.le_trans _ _ _ Hsmall Hsquare)) as Hlog.
        rewrite Nat.log2_pow2 in Hlog by lia. exact Hlog. }
      eapply Nat.le_trans; [apply Nat.mul_le_mono_l; exact Hlog|].
      replace ((supp m + 1)^2 * (2 * b m)) with
        (2 * ((supp m + 1)^2 * b m)) by ring. lia.
    - assert (Hlinear : Nat.log2 nodes <= (b m + Nat.log2 nodes + 1)^2).
      { eapply Nat.le_trans with (b m + Nat.log2 nodes + 1); [lia|].
        cbn [Nat.pow]. rewrite Nat.mul_1_r.
        replace (b m + Nat.log2 nodes + 1) with
          ((b m + Nat.log2 nodes + 1) * 1) at 1 by lia.
        apply Nat.mul_le_mono; [apply Nat.le_refl|lia]. }
      eapply Nat.le_trans with ((nodes + 1) * (b m + Nat.log2 nodes + 1)^2).
      + apply Nat.mul_le_mono; [lia|exact Hlinear].
      + lia.
  Qed.

  (** The range endpoint allowance fits assignment's two frozen structural work terms. *)
  Lemma assign_range_update_work : forall x e m,
    (supp m + 1)^2 * (b m + ell m + 4 * X.bits x + range_bits e (Reached m) + 3) <=
      8 * ((supp m + 1)^2 *
        (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1) +
        (tsize e + 1) * (range_payload e m)^2).
  Proof.
    intros x e m.
    pose proof (support_log_work m (tsize e)) as Hlog.
    assert (Hsource : (tsize e + 1) * (b m + Nat.log2 (tsize e) + 1)^2 <=
      (tsize e + 1) * (range_payload e m)^2).
    { apply Nat.mul_le_mono_l. cbn [Nat.pow]. rewrite !Nat.mul_1_r.
      apply Nat.mul_le_mono; unfold range_payload; lia. }
    assert (Hkey : (supp m + 1)^2 * b m <=
      (supp m + 1)^2 *
        (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1)).
    { apply Nat.mul_le_mono_l. lia. }
    assert (Hpayload : b m + ell m + 4 * X.bits x + range_bits e (Reached m) + 3 <=
      5 * (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1) +
        Nat.log2 (tsize e)).
    { unfold range_bits, ells. lia. }
    assert (Hmatrix :
      (supp m + 1)^2 * (b m + ell m + 4 * X.bits x + range_bits e (Reached m) + 3) <=
      5 * ((supp m + 1)^2 *
        (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1)) +
        (supp m + 1)^2 * Nat.log2 (tsize e)).
    { replace (5 * ((supp m + 1)^2 *
        (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1)) +
        (supp m + 1)^2 * Nat.log2 (tsize e)) with
        ((supp m + 1)^2 *
          (5 * (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1) +
            Nat.log2 (tsize e))) by ring.
      now apply Nat.mul_le_mono_l. }
    set (matrix_work := (supp m + 1)^2 *
      (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1)) in *.
    set (source_work := (tsize e + 1) * (range_payload e m)^2) in *.
    clear Hpayload. clearbody matrix_work source_work. lia.
  Qed.

  (** Copy dispatch is covered by one source range charge. *)
  Lemma T_copy_source_range : forall e m f r,
    F.lin_of e = Some (f, r) ->
    (T_copy_source f <= 32 * range_unit e m)%N.
  Proof.
    intros e m f r Hlin. destruct (F.lin_of_size e f r Hlin) as [_ Hbits].
    eapply N.le_trans; [apply T_copy_source_le|].
    apply N.mul_le_mono_l. apply range_linear_charge. unfold range_payload. lia.
  Qed.

  (** Signed copy permission examines only the recognized form variable. *)
  Lemma T_copy_allowed_source : forall x e m f r source,
    F.lin_of e = Some (f, r) -> copy_source f = Some source ->
    (T_copy_allowed x source <= 8 * (X.c_key + 1) * range_unit e m)%N.
  Proof.
    intros x e m f r source Hlin Hsource.
    pose proof (copy_source_form_bits f source Hsource) as Hsource_bits.
    destruct (F.lin_of_size e f r Hlin) as [_ Hbits].
    eapply N.le_trans; [apply T_copy_allowed_le|].
    apply N.mul_le_mono_l. apply range_linear_charge. unfold range_payload. lia.
  Qed.

  (** Wrapping exactness checks fit the same bit allowance as source accumulation. *)
  Lemma T_wrap_exact_range : forall e m f r,
    F.lin_of e = Some (f, r) ->
    (T_rel_wrap_exact r (form_bounds m f) <= 48 * range_unit e m)%N.
  Proof.
    intros e m f r Hlin. destruct (F.lin_of_size e f r Hlin) as [_ Hbits].
    eapply N.le_trans.
    - apply rel_wrap_exact_time with (bits_r := F.bits_e e)
        (bits_a := range_bits e (Reached m)).
      + change (F.wrap_bits r <= F.bits_e e). lia.
      + now apply (form_range_abs e m f r).
    - replace (48 * range_unit e m)%N with (16 * (3 * range_unit e m))%N by ring.
      apply N.mul_le_mono_l. eapply N.le_trans with (N.of_nat (3 * range_payload e m)).
      + apply time_of_nat_le. unfold range_bits, ells, range_payload. lia.
      + rewrite Nat2N.inj_mul. change (3 * N.of_nat (range_payload e m) <=
          3 * range_unit e m)%N.
        apply N.mul_le_mono_l. apply range_unit_linear.
  Qed.

  (** Assignment's structural work separates matrix updates from source interval arithmetic. *)
  Definition assign_unit (x : X.t) (e : term L.op X.t) (m : dbm) : N :=
    N.of_nat ((supp m + 1)^2 *
      (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1) + skel m + M.weight m +
      (tsize e + 1) * (range_payload e m)^2).

  (** This private coefficient covers each performed assignment phase. *)
  Definition k_assign : N :=
    (1099511627776 * (M.c_map + K.c_key + X.c_key + 1) *
      (M.c_map + K.c_key + X.c_key + 1))%N.

  (** Assignment's matrix term contains a nonzero arithmetic unit. *)
  Lemma assign_unit_positive : forall x e m, (1 <= assign_unit x e m)%N.
  Proof.
    intros x e m. unfold assign_unit.
    apply (time_of_nat_le 1%nat _).
    assert (Hmatrix : 1 <= (supp m + 1)^2 *
      (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1)).
    { cbn [Nat.pow]. nia. }
    lia.
  Qed.

  (** The frozen assignment work includes its entire quadratic matrix allowance. *)
  Lemma assign_unit_matrix : forall x e m,
    (N.of_nat ((supp m + 1)^2 *
      (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1)) <=
      assign_unit x e m)%N.
  Proof.
    intros x e m. unfold assign_unit. apply time_of_nat_le. lia.
  Qed.

  (** Signed matrix labels are included alongside the quadratic update allowance. *)
  Lemma assign_unit_matrix_labels : forall x e m,
    (N.of_nat ((supp m + 1)^2 *
      (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1) + M.weight m) <=
      assign_unit x e m)%N.
  Proof.
    intros x e m. unfold assign_unit. apply time_of_nat_le. lia.
  Qed.

  (** The source interval allowance is another summand of assignment's structural work. *)
  Lemma assign_unit_source : forall x e m,
    (N.of_nat ((tsize e + 1)%nat) * range_unit e m <= assign_unit x e m)%N.
  Proof.
    intros x e m. unfold range_unit. rewrite <- Nat2N.inj_mul.
    unfold assign_unit. apply time_of_nat_le. lia.
  Qed.

  (** One source arithmetic charge fits the complete assignment allowance. *)
  Lemma assign_unit_range : forall x e m, (range_unit e m <= assign_unit x e m)%N.
  Proof.
    intros x e m. eapply N.le_trans; [|apply assign_unit_source].
    replace (range_unit e m) with (1 * range_unit e m)%N at 1 by ring.
    apply N.mul_le_mono_r.
    change (N.of_nat 1%nat <= N.of_nat (tsize e + 1))%N.
    apply time_of_nat_le. lia.
  Qed.

  (** The source fold fits one assignment phase charge. *)
  Lemma T_form_bounds_assign : forall x e m f r,
    F.lin_of e = Some (f, r) ->
    (T_form_bounds m f <= k_assign * assign_unit x e m)%N.
  Proof.
    intros x e m f r Hlin. eapply N.le_trans; [now apply (T_form_bounds_source e m f r)|].
    apply N.mul_le_mono.
    - unfold k_assign. nia.
    - apply assign_unit_source.
  Qed.

  (** Source dispatch and wrap tests are small compared with an assignment phase. *)
  Lemma assignment_source_tests : forall x e m f r,
    F.lin_of e = Some (f, r) ->
    (T_copy_source f <= k_assign * assign_unit x e m)%N /\
    (T_rel_wrap_exact r (form_bounds m f) <= k_assign * assign_unit x e m)%N /\
    (T_rel_wrap_bounds r (form_bounds m f) <= k_assign * assign_unit x e m)%N.
  Proof.
    intros x e m f r Hlin. split.
    - eapply N.le_trans; [now apply (T_copy_source_range e m f r)|].
      apply N.mul_le_mono; [unfold k_assign; nia|apply assign_unit_range].
    - split.
      + eapply N.le_trans; [now apply (T_wrap_exact_range e m f r)|].
        apply N.mul_le_mono; [unfold k_assign; nia|apply assign_unit_range].
      + eapply N.le_trans; [now apply (T_wrap_bounds_range e m f r)|].
        apply N.mul_le_mono; [unfold k_assign; nia|apply assign_unit_range].
  Qed.

  (** The signed-copy permission test fits one assignment phase. *)
  Lemma T_copy_allowed_assign : forall x e m f r source,
    F.lin_of e = Some (f, r) -> copy_source f = Some source ->
    (T_copy_allowed x source <= k_assign * assign_unit x e m)%N.
  Proof.
    intros x e m f r source Hlin Hsource.
    eapply N.le_trans; [now apply (T_copy_allowed_source x e m f r source)|].
    apply N.mul_le_mono; [unfold k_assign; nia|apply assign_unit_range].
  Qed.

  (** Havoc's sparse traversal fits a small fraction of the assignment matrix term. *)
  Lemma T_havoc_assign_small : forall x e m,
    (T_havoc x (Reached m) <=
      1024 * (M.c_map + 1) * (M.c_map + 1) * assign_unit x e m)%N.
  Proof.
    intros x e m. pose proof (T_havoc_small x m) as Htime.
    assert (Hmatrix : (supp m + 1) * (b m + X.bits x + 4) + 1 <=
      8 * ((supp m + 1)^2 *
        (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1))).
    { clear Htime. cbn [Nat.pow]. nia. }
    pose proof (time_of_nat_le _ _ Hmatrix) as Hmatrix_cast.
    rewrite (Nat2N.inj_mul 8 _) in Hmatrix_cast.
    assert (Hwork : (N.of_nat ((supp m + 1) * (b m + X.bits x + 4) + 1) <=
      8 * assign_unit x e m)%N).
    { eapply N.le_trans; [exact Hmatrix_cast|].
      apply N.mul_le_mono_l. apply assign_unit_matrix. }
    eapply N.le_trans; [exact Htime|].
    replace (1024 * (M.c_map + 1) * (M.c_map + 1) * assign_unit x e m)%N with
      (128 * (M.c_map + 1) * (M.c_map + 1) * (8 * assign_unit x e m))%N by ring.
    now apply N.mul_le_mono_l.
  Qed.

  (** Assignment pays signed interval refinements after resource-decreasing havoc. *)
  Lemma T_add_range_assign : forall x e m f r,
    F.lin_of e = Some (f, r) ->
    (T_add_range x (rel_wrap_bounds r (form_bounds m f)) (havoc x (Reached m)) <=
      k_assign * assign_unit x e m)%N.
  Proof.
    intros x e m f r Hlin.
    pose proof (range_abs e (Reached m)) as Hbounds.
    unfold range in Hbounds. rewrite Hlin in Hbounds.
    pose proof (T_add_range_small x (rel_wrap_bounds r (form_bounds m f))
      (havoc x (Reached m)) (range_bits e (Reached m)) Hbounds) as Htime.
    set (forgotten := havoc x (Reached m)) in *.
    destruct (havoc_resources x (Reached m)) as [Hcount [Hbits [Hell Hlabels]]].
    fold forgotten in Hcount, Hbits, Hell, Hlabels.
    change (ns forgotten <= supp m) in Hcount.
    change (bs forgotten <= b m) in Hbits.
    change (ells forgotten <= ell m) in Hell.
    change (labs forgotten <= M.weight m) in Hlabels.
    assert (Hsquare : (ns forgotten + 1)^2 <= (supp m + 1)^2).
    { cbn [Nat.pow]. rewrite !Nat.mul_1_r. apply Nat.mul_le_mono; lia. }
    assert (Hmatrix : (ns forgotten + 1)^2 *
      (bs forgotten + ells forgotten + 4 * X.bits x + range_bits e (Reached m) + 3) +
      labs forgotten <=
      (supp m + 1)^2 *
        (b m + ell m + 4 * X.bits x + range_bits e (Reached m) + 3) + M.weight m).
    { apply Nat.add_le_mono; [apply Nat.mul_le_mono; [exact Hsquare|lia]|exact Hlabels]. }
    pose proof (assign_range_update_work x e m) as Hmixed.
    assert (Hwork : (ns forgotten + 1)^2 *
      (bs forgotten + ells forgotten + 4 * X.bits x + range_bits e (Reached m) + 3) +
      labs forgotten <=
      8 * ((supp m + 1)^2 *
        (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1) + skel m + M.weight m +
        (tsize e + 1) * (range_payload e m)^2)) by lia.
    pose proof (time_of_nat_le _ _ Hwork) as Hcast.
    rewrite (Nat2N.inj_mul 8 _) in Hcast.
    change (N.of_nat ((ns forgotten + 1)^2 *
      (bs forgotten + ells forgotten + 4 * X.bits x + range_bits e (Reached m) + 3) +
      labs forgotten) <= 8 * assign_unit x e m)%N in Hcast.
    eapply N.le_trans; [exact Htime|].
    eapply N.le_trans with (512 * c_octagon * (8 * assign_unit x e m))%N.
    - now apply N.mul_le_mono_l.
    - replace (512 * c_octagon * (8 * assign_unit x e m))%N with
        (4096 * c_octagon * assign_unit x e m)%N by ring.
      apply N.mul_le_mono_r.
      pose proof (N.le_0_l M.c_map) as Hmap_nonnegative. clear -Hmap_nonnegative.
      unfold k_assign, c_octagon. nia.
  Qed.

  (** A recognized copy pays either one self shift or havoc and two affine refinements. *)
  Lemma T_assign_copy_source : forall x e m f r source,
    F.lin_of e = Some (f, r) -> copy_source f = Some source ->
    (T_assign_copy x source (cst f) (Reached m) <=
      k_assign * assign_unit x e m)%N.
  Proof.
    intros x e m f r source Hlin Hsource.
    destruct (F.lin_of_size e f r Hlin) as [_ Hbits].
    assert (Hconstant : Z.size_nat (cst f) <= F.bits_e e).
    { pose proof (form_bits_constant f). lia. }
    assert (Hsource_bits : K.bits source <= 2 * F.bits_e e + 1).
    { pose proof (copy_source_key_bits f source Hsource). lia. }
    set (forgotten := havoc x (Reached m)).
    destruct (havoc_resources x (Reached m)) as [Hcount [Hkeys [Hentries Hlabels]]].
    fold forgotten in Hcount, Hkeys, Hentries, Hlabels.
    change (ns forgotten <= supp m) in Hcount.
    change (bs forgotten <= b m) in Hkeys.
    change (ells forgotten <= ell m) in Hentries.
    change (labs forgotten <= M.weight m) in Hlabels.
    assert (Hsquare : (ns forgotten + 1)^2 <= (supp m + 1)^2).
    { cbn [Nat.pow]. rewrite !Nat.mul_1_r. apply Nat.mul_le_mono; lia. }
    assert (Hpayload :
      bs forgotten + ells forgotten + K.bits source + K.bits (x, true) + F.bits_e e + 1 <=
      3 * (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1)).
    { pose proof (signed_bits_le x true). lia. }
    assert (Hpair_matrix : (ns forgotten + 1)^2 *
      (bs forgotten + ells forgotten + K.bits source + K.bits (x, true) + F.bits_e e + 1) <=
      3 * ((supp m + 1)^2 *
        (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1))).
    { replace (3 * ((supp m + 1)^2 *
        (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1))) with
        ((supp m + 1)^2 *
          (3 * (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1))) by ring.
      now apply Nat.mul_le_mono. }
    assert (Hpair_work : (ns forgotten + 1)^2 *
      (bs forgotten + ells forgotten + K.bits source + K.bits (x, true) + F.bits_e e + 1) +
      labs forgotten <=
      3 * ((supp m + 1)^2 *
        (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1) + M.weight m)) by lia.
    pose proof (time_of_nat_le _ _ Hpair_work) as Hpair_cast.
    rewrite (Nat2N.inj_mul 3 _) in Hpair_cast.
    assert (Hpair_allowance : (N.of_nat ((ns forgotten + 1)^2 *
      (bs forgotten + ells forgotten + K.bits source + K.bits (x, true) + F.bits_e e + 1) +
      labs forgotten) <= 3 * assign_unit x e m)%N).
    { eapply N.le_trans; [exact Hpair_cast|].
      apply N.mul_le_mono_l. apply assign_unit_matrix_labels. }
    assert (Hpair : (T_refine source (x, true) (cst f) forgotten +
      T_refine (x, true) source (-cst f)%Z (refine source (x, true) (cst f) forgotten) <=
      768 * c_octagon * assign_unit x e m)%N).
    { eapply N.le_trans.
      - apply T_refine_pair_small with (bits := F.bits_e e).
        + exact Hconstant.
        + now rewrite zbits_opp.
      - replace (768 * c_octagon * assign_unit x e m)%N with
          (256 * c_octagon * (3 * assign_unit x e m))%N by ring.
        now apply N.mul_le_mono_l. }
    assert (Hshift : (T_shift x (cst f) m <=
      2048 * (M.c_map + 1) * (M.c_map + 1) * assign_unit x e m)%N).
    { eapply N.le_trans; [apply T_shift_le|]. apply N.mul_le_mono_l.
      eapply N.le_trans; [|apply assign_unit_matrix].
      apply time_of_nat_le, Nat.mul_le_mono_l. lia. }
    pose proof (quadratic_payload_le (supp m)
      (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1)) as Hquadratic.
    assert (Hkey_work : K.bits source + 1 <=
      2 * ((supp m + 1)^2 *
        (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1))) by lia.
    pose proof (time_of_nat_le _ _ Hkey_work) as Hkey_cast.
    rewrite (Nat2N.inj_mul 2 _) in Hkey_cast.
    assert (Hkey_allowance : (N.of_nat (K.bits source + 1) <= 2 * assign_unit x e m)%N).
    { eapply N.le_trans; [exact Hkey_cast|].
      apply N.mul_le_mono_l. apply assign_unit_matrix. }
    assert (Hequal : (K.T_eqb source (x, true) <= 2 * K.c_key * assign_unit x e m)%N).
    { eapply N.le_trans; [apply K.T_eqb_le|].
      replace (2 * K.c_key * assign_unit x e m)%N with
        (K.c_key * (2 * assign_unit x e m))%N by ring.
      now apply N.mul_le_mono_l. }
    pose proof (T_havoc_assign_small x e m) as Hhavoc.
    pose proof (Z.T_opp_le (cst f)) as Hopp.
    pose proof (assign_unit_positive x e m) as Hpositive.
    assert (Hcoefficient : (8 + 2 * K.c_key +
      2048 * (M.c_map + 1) * (M.c_map + 1) +
      1024 * (M.c_map + 1) * (M.c_map + 1) + 768 * c_octagon <= k_assign)%N).
    { pose proof (N.le_0_l M.c_map) as Hmap_nonnegative. clear -Hmap_nonnegative.
      unfold k_assign, c_octagon. nia. }
    pose proof (N.mul_le_mono_r _ _ (assign_unit x e m) Hcoefficient) as Hbudget.
    rewrite !N.mul_add_distr_r in Hbudget.
    clear Hbits Hconstant Hsource_bits Hcount Hkeys Hentries Hlabels Hsquare Hpayload
      Hpair_matrix Hpair_work Hpair_cast Hpair_allowance Hquadratic Hkey_work Hkey_cast
      Hkey_allowance Hcoefficient.
    set (work := assign_unit x e m) in *. clearbody work.
    time_unfold (@T_assign_copy). time_simpl. cbn beta iota zeta.
    destruct (K.eqb source (x, true)); cbn beta iota zeta; fold forgotten; lia.
  Qed.

  (** A source logarithm is paid by support key bits or by the source-size allowance. *)
  Lemma support_log_linear : forall m nodes,
    (supp m + 1) * Nat.log2 nodes <=
      2 * ((supp m + 1) * b m) +
        (nodes + 1) * (b m + Nat.log2 nodes + 1)^2.
  Proof.
    intros m nodes. destruct (Nat.le_gt_cases nodes (supp m + 1)) as [Hsmall|Hlarge].
    - assert (Hlog : Nat.log2 nodes <= b m).
      { eapply Nat.le_trans; [apply Nat.log2_le_mono; exact Hsmall|].
        apply log2_support_le. }
      eapply Nat.le_trans; [apply Nat.mul_le_mono_l; exact Hlog|]. lia.
    - assert (Hlinear : Nat.log2 nodes <= (b m + Nat.log2 nodes + 1)^2).
      { eapply Nat.le_trans with (b m + Nat.log2 nodes + 1); [lia|].
        cbn [Nat.pow]. nia. }
      eapply Nat.le_trans with ((nodes + 1) * (b m + Nat.log2 nodes + 1)^2).
      + apply Nat.mul_le_mono; [lia|exact Hlinear].
      + lia.
  Qed.

  (** Fast assignment separates linear matrix updates from source interval arithmetic. *)
  Definition fast_assign_unit (x : X.t) (e : term L.op X.t) (m : dbm) : N :=
    N.of_nat ((supp m + 1) *
      (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1) + skel m + M.weight m +
      (tsize e + 1) * (range_payload e m)^2).

  (** The range endpoint allowance fits assignment's two linear-update and source work terms. *)
  Lemma assign_range_update_linear : forall x e m,
    (supp m + 1) * (b m + ell m + 4 * X.bits x + range_bits e (Reached m) + 3) <=
      8 * ((supp m + 1) *
        (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1) +
        (tsize e + 1) * (range_payload e m)^2).
  Proof.
    intros x e m.
    pose proof (support_log_linear m (tsize e)) as Hlog.
    assert (Hsource : (tsize e + 1) * (b m + Nat.log2 (tsize e) + 1)^2 <=
      (tsize e + 1) * (range_payload e m)^2).
    { apply Nat.mul_le_mono_l. cbn [Nat.pow]. rewrite !Nat.mul_1_r.
      apply Nat.mul_le_mono; unfold range_payload; lia. }
    assert (Hkey : (supp m + 1) * b m <=
      (supp m + 1) *
        (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1)).
    { apply Nat.mul_le_mono_l. lia. }
    assert (Hpayload : b m + ell m + 4 * X.bits x + range_bits e (Reached m) + 3 <=
      5 * (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1) +
        Nat.log2 (tsize e)).
    { unfold range_bits, ells. lia. }
    assert (Hmatrix :
      (supp m + 1) * (b m + ell m + 4 * X.bits x + range_bits e (Reached m) + 3) <=
      5 * ((supp m + 1) *
        (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1)) +
        (supp m + 1) * Nat.log2 (tsize e)).
    { replace (5 * ((supp m + 1) *
        (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1)) +
        (supp m + 1) * Nat.log2 (tsize e)) with
        ((supp m + 1) *
          (5 * (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1) +
            Nat.log2 (tsize e))) by ring.
      now apply Nat.mul_le_mono_l. }
    set (matrix_work := (supp m + 1) *
      (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1)) in *.
    set (source_work := (tsize e + 1) * (range_payload e m)^2) in *.
    clear Hpayload. clearbody matrix_work source_work. lia.
  Qed.

  (** Assignment's matrix term contains a nonzero arithmetic unit. *)
  Lemma fast_assign_unit_positive : forall x e m, (1 <= fast_assign_unit x e m)%N.
  Proof.
    intros x e m. unfold fast_assign_unit.
    apply (time_of_nat_le 1%nat _).
    assert (Hmatrix : 1 <= (supp m + 1) *
      (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1)).
    { cbn [Nat.pow]. nia. }
    lia.
  Qed.

  (** The frozen assignment work includes its entire linear matrix allowance. *)
  Lemma fast_assign_unit_matrix : forall x e m,
    (N.of_nat ((supp m + 1) *
      (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1)) <=
      fast_assign_unit x e m)%N.
  Proof.
    intros x e m. unfold fast_assign_unit. apply time_of_nat_le. lia.
  Qed.

  (** Signed matrix labels are included alongside the linear update allowance. *)
  Lemma fast_assign_unit_matrix_labels : forall x e m,
    (N.of_nat ((supp m + 1) *
      (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1) + M.weight m) <=
      fast_assign_unit x e m)%N.
  Proof.
    intros x e m. unfold fast_assign_unit. apply time_of_nat_le. lia.
  Qed.

  (** The source interval allowance is another summand of assignment's structural work. *)
  Lemma fast_assign_unit_source : forall x e m,
    (N.of_nat ((tsize e + 1)%nat) * range_unit e m <= fast_assign_unit x e m)%N.
  Proof.
    intros x e m. unfold range_unit. rewrite <- Nat2N.inj_mul.
    unfold fast_assign_unit. apply time_of_nat_le. lia.
  Qed.

  (** One source arithmetic charge fits the complete assignment allowance. *)
  Lemma fast_assign_unit_range : forall x e m, (range_unit e m <= fast_assign_unit x e m)%N.
  Proof.
    intros x e m. eapply N.le_trans; [|apply fast_assign_unit_source].
    replace (range_unit e m) with (1 * range_unit e m)%N at 1 by ring.
    apply N.mul_le_mono_r.
    change (N.of_nat 1%nat <= N.of_nat (tsize e + 1))%N.
    apply time_of_nat_le. lia.
  Qed.

  (** The source fold fits one assignment phase charge. *)
  Lemma T_form_bounds_fast_assign : forall x e m f r,
    F.lin_of e = Some (f, r) ->
    (T_form_bounds m f <= k_assign * fast_assign_unit x e m)%N.
  Proof.
    intros x e m f r Hlin. eapply N.le_trans; [now apply (T_form_bounds_source e m f r)|].
    apply N.mul_le_mono.
    - unfold k_assign. nia.
    - apply fast_assign_unit_source.
  Qed.

  (** Source dispatch and wrap tests are small compared with an assignment phase. *)
  Lemma assignment_fast_source_tests : forall x e m f r,
    F.lin_of e = Some (f, r) ->
    (T_copy_source f <= k_assign * fast_assign_unit x e m)%N /\
    (T_rel_wrap_exact r (form_bounds m f) <= k_assign * fast_assign_unit x e m)%N /\
    (T_rel_wrap_bounds r (form_bounds m f) <= k_assign * fast_assign_unit x e m)%N.
  Proof.
    intros x e m f r Hlin. split.
    - eapply N.le_trans; [now apply (T_copy_source_range e m f r)|].
      apply N.mul_le_mono; [unfold k_assign; nia|apply fast_assign_unit_range].
    - split.
      + eapply N.le_trans; [now apply (T_wrap_exact_range e m f r)|].
        apply N.mul_le_mono; [unfold k_assign; nia|apply fast_assign_unit_range].
      + eapply N.le_trans; [now apply (T_wrap_bounds_range e m f r)|].
        apply N.mul_le_mono; [unfold k_assign; nia|apply fast_assign_unit_range].
  Qed.

  (** The signed-copy permission test fits one assignment phase. *)
  Lemma T_copy_allowed_fast_assign : forall x e m f r source,
    F.lin_of e = Some (f, r) -> copy_source f = Some source ->
    (T_copy_allowed x source <= k_assign * fast_assign_unit x e m)%N.
  Proof.
    intros x e m f r source Hlin Hsource.
    eapply N.le_trans; [now apply (T_copy_allowed_source x e m f r source)|].
    apply N.mul_le_mono; [unfold k_assign; nia|apply fast_assign_unit_range].
  Qed.

  (** Havoc's sparse traversal fits a small fraction of the assignment matrix term. *)
  Lemma T_havoc_fast_assign_small : forall x e m,
    (T_havoc x (Reached m) <=
      1024 * (M.c_map + 1) * (M.c_map + 1) * fast_assign_unit x e m)%N.
  Proof.
    intros x e m. pose proof (T_havoc_small x m) as Htime.
    assert (Hmatrix : (supp m + 1) * (b m + X.bits x + 4) + 1 <=
      8 * ((supp m + 1) *
        (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1))).
    { clear Htime. cbn [Nat.pow]. nia. }
    pose proof (time_of_nat_le _ _ Hmatrix) as Hmatrix_cast.
    rewrite (Nat2N.inj_mul 8 _) in Hmatrix_cast.
    assert (Hwork : (N.of_nat ((supp m + 1) * (b m + X.bits x + 4) + 1) <=
      8 * fast_assign_unit x e m)%N).
    { eapply N.le_trans; [exact Hmatrix_cast|].
      apply N.mul_le_mono_l. apply fast_assign_unit_matrix. }
    eapply N.le_trans; [exact Htime|].
    replace (1024 * (M.c_map + 1) * (M.c_map + 1) * fast_assign_unit x e m)%N with
      (128 * (M.c_map + 1) * (M.c_map + 1) * (8 * fast_assign_unit x e m))%N by ring.
    now apply N.mul_le_mono_l.
  Qed.

  (** The public numeric coefficient covers every signed assignment phase. *)
  Lemma assign_public_budget : forall work lin_cost : N,
    (8 + lin_cost + 8 * (k_assign * work) <= c_num * (work + lin_cost + 1))%N.
  Proof.
    intros work lin_cost.
    assert (Hphase : (8 * k_assign <= c_num)%N) by (unfold k_assign, c_num; nia).
    assert (Hconstant : (8 <= c_num)%N) by (unfold c_num; nia).
    pose proof (N.mul_le_mono_r _ _ work Hphase) as Hwork.
    replace (8 * k_assign * work)%N with (8 * (k_assign * work))%N in Hwork by ring.
    assert (Hlinear : (lin_cost <= c_num * lin_cost)%N).
    { replace lin_cost with (1 * lin_cost)%N at 1 by ring.
      apply N.mul_le_mono_r. lia. }
    replace (c_num * (work + lin_cost + 1))%N with
      (c_num * work + c_num * lin_cost + c_num)%N by ring. lia.
  Qed.

  (** Fast interval updates follow resource-decreasing havoc within one assignment phase. *)
  Lemma T_add_range_fast_assign : forall x e m f r,
    F.lin_of e = Some (f, r) ->
    (T_add_range_fast x (rel_wrap_bounds r (form_bounds m f)) (havoc x (Reached m)) <=
      k_assign * fast_assign_unit x e m)%N.
  Proof.
    intros x e m f r Hlin.
    pose proof (range_abs e (Reached m)) as Hbounds.
    unfold range in Hbounds. rewrite Hlin in Hbounds.
    pose proof (T_add_range_fast_small x (rel_wrap_bounds r (form_bounds m f))
      (havoc x (Reached m)) (range_bits e (Reached m)) Hbounds) as Htime.
    set (forgotten := havoc x (Reached m)) in *.
    destruct (havoc_resources x (Reached m)) as [Hcount [Hbits [Hell Hlabels]]].
    fold forgotten in Hcount, Hbits, Hell, Hlabels.
    change (ns forgotten <= supp m) in Hcount.
    change (bs forgotten <= b m) in Hbits.
    change (ells forgotten <= ell m) in Hell.
    change (labs forgotten <= M.weight m) in Hlabels.
    assert (Hmatrix : (ns forgotten + 1) *
      (bs forgotten + ells forgotten + 4 * X.bits x + range_bits e (Reached m) + 3) +
      labs forgotten <=
      (supp m + 1) *
        (b m + ell m + 4 * X.bits x + range_bits e (Reached m) + 3) + M.weight m).
    { apply Nat.add_le_mono; [apply Nat.mul_le_mono; lia|exact Hlabels]. }
    pose proof (assign_range_update_linear x e m) as Hmixed.
    assert (Hwork : (ns forgotten + 1) *
      (bs forgotten + ells forgotten + 4 * X.bits x + range_bits e (Reached m) + 3) +
      labs forgotten <=
      8 * ((supp m + 1) *
        (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1) + skel m + M.weight m +
        (tsize e + 1) * (range_payload e m)^2)) by lia.
    pose proof (time_of_nat_le _ _ Hwork) as Hcast.
    rewrite (Nat2N.inj_mul 8 _) in Hcast.
    change (N.of_nat ((ns forgotten + 1) *
      (bs forgotten + ells forgotten + 4 * X.bits x + range_bits e (Reached m) + 3) +
      labs forgotten) <= 8 * fast_assign_unit x e m)%N in Hcast.
    eapply N.le_trans; [exact Htime|].
    eapply N.le_trans with (512 * c_octagon * (8 * fast_assign_unit x e m))%N.
    - now apply N.mul_le_mono_l.
    - replace (512 * c_octagon * (8 * fast_assign_unit x e m))%N with
        (4096 * c_octagon * fast_assign_unit x e m)%N by ring.
      apply N.mul_le_mono_r. unfold k_assign, c_octagon. nia.
  Qed.

  (** A recognized source copy fits the linear support allowance of its expression. *)
  Lemma T_assign_copy_fast_source : forall x e m f r source,
    F.lin_of e = Some (f, r) -> copy_source f = Some source ->
    (T_assign_copy_fast x source (cst f) (Reached m) <=
      k_assign * fast_assign_unit x e m)%N.
  Proof.
    intros x e m f r source Hlin Hsource.
    destruct (F.lin_of_size e f r Hlin) as [_ Hbits].
    assert (Hconstant : Z.size_nat (cst f) <= F.bits_e e).
    { pose proof (form_bits_constant f). lia. }
    assert (Hsource_bits : K.bits source <= 2 * F.bits_e e + 1).
    { pose proof (copy_source_key_bits f source Hsource). lia. }
    assert (Hmatrix : (supp m + 1) *
      (b m + ell m + X.bits x + K.bits source + Z.size_nat (cst f) + 1) <=
      3 * ((supp m + 1) *
        (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1))).
    { replace (3 * ((supp m + 1) *
        (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1))) with
        ((supp m + 1) *
          (3 * (b m + ell m + X.bits x + F.bits_e e + lin_bits e + 1))) by ring.
      apply Nat.mul_le_mono_l. lia. }
    pose proof (time_of_nat_le _ _ Hmatrix) as Hcast.
    rewrite (Nat2N.inj_mul 3 _) in Hcast.
    assert (Hwork : (N.of_nat ((supp m + 1) *
      (b m + ell m + X.bits x + K.bits source + Z.size_nat (cst f) + 1)) <=
      3 * fast_assign_unit x e m)%N).
    { eapply N.le_trans; [exact Hcast|].
      apply N.mul_le_mono_l. apply fast_assign_unit_matrix. }
    eapply N.le_trans; [apply T_assign_copy_fast_small|].
    eapply N.le_trans with
      ((1024 * 1024) * (M.c_map + K.c_key + 1) * (M.c_map + K.c_key + 1) *
        (3 * fast_assign_unit x e m))%N.
    - now apply N.mul_le_mono_l.
    - replace ((1024 * 1024) * (M.c_map + K.c_key + 1) * (M.c_map + K.c_key + 1) *
        (3 * fast_assign_unit x e m))%N with
        ((3 * (1024 * 1024) * (M.c_map + K.c_key + 1) * (M.c_map + K.c_key + 1)) *
          fast_assign_unit x e m)%N by ring.
      apply N.mul_le_mono_r. unfold k_assign. nia.
  Qed.

  (** Every branch of fast assignment fits the linear matrix and source allowances. *)
  Lemma T_assign_fast_bound : forall x e m,
    (T_assign x e (Reached m) <=
      c_num * (fast_assign_unit x e m + F.T_lin_of e + 1))%N.
  Proof.
    intros x e m. set (work := fast_assign_unit x e m).
    assert (Hhavoc : (T_havoc x (Reached m) <= k_assign * work)%N).
    { eapply N.le_trans; [apply T_havoc_fast_assign_small|].
      apply N.mul_le_mono_r. unfold k_assign. nia. }
    eapply N.le_trans; [|exact (assign_public_budget work (F.T_lin_of e))].
    time_unfold (@T_assign). time_simpl. cbn beta iota zeta.
    destruct (F.lin_of e) as [[f r]|] eqn:Hlin.
    - assert (Hform : (T_form_bounds m f <= k_assign * work)%N).
      { now apply (T_form_bounds_fast_assign x e m f r). }
      destruct (assignment_fast_source_tests x e m f r Hlin) as [Hcopy [Hexact Hwrap]].
      change (T_copy_source f <= k_assign * work)%N in Hcopy.
      change (T_rel_wrap_exact r (form_bounds m f) <= k_assign * work)%N in Hexact.
      change (T_rel_wrap_bounds r (form_bounds m f) <= k_assign * work)%N in Hwrap.
      assert (Hrange : (T_add_range_fast x (rel_wrap_bounds r (form_bounds m f))
        (havoc x (Reached m)) <= k_assign * work)%N).
      { now apply (T_add_range_fast_assign x e m f r). }
      destruct (copy_source f) as [source|] eqn:Hsource.
      + assert (Hassign_copy : (T_assign_copy_fast x source (cst f) (Reached m) <=
          k_assign * work)%N).
        { now apply (T_assign_copy_fast_source x e m f r source). }
        assert (Hallowed : (T_copy_allowed x source <= k_assign * work)%N).
        { now apply (T_copy_allowed_fast_assign x e m f r source). }
        set (charge := (k_assign * work)%N) in *.
        clearbody charge work.
        destruct (copy_allowed x source); cbn beta iota zeta.
        * destruct (rel_wrap_exact r (form_bounds m f));
            time_simpl; cbn beta iota zeta; lia.
        * time_simpl. cbn beta iota zeta. lia.
      + set (charge := (k_assign * work)%N) in *.
        clearbody charge work. time_simpl. cbn beta iota zeta. lia.
    - set (charge := (k_assign * work)%N) in *.
      clearbody charge work. time_simpl. cbn beta iota zeta. lia.
  Qed.

  (** The linear assignment allowance is covered by the previous quadratic allowance. *)
  Lemma fast_assign_unit_le : forall x e m,
    (fast_assign_unit x e m <= assign_unit x e m)%N.
  Proof.
    intros x e m. unfold fast_assign_unit, assign_unit. apply time_of_nat_le.
    apply Nat.add_le_mono_r, Nat.add_le_mono_r, Nat.add_le_mono_r, Nat.mul_le_mono_r.
    cbn [Nat.pow]. nia.
  Qed.

  (** Numeric assignment charges its performed source work and bounded sparse updates. *)
  Lemma T_assign_le : forall x e s,
    (T_assign x e s <= c_num * N.of_nat (assign_work x e s + 1))%N.
  Proof.
    intros x e [|m].
    - assert (Hpositive : (1 <= c_num)%N) by (unfold c_num; nia).
      assert (Hwork : (1 <= N.of_nat (assign_work x e Unreached + 1))%N).
      { change (N.of_nat 1%nat <= N.of_nat (assign_work x e Unreached + 1))%N.
        apply time_of_nat_le. lia. }
      pose proof (N.mul_le_mono _ _ _ _ Hpositive Hwork) as Hbudget.
      time_unfold (@T_assign). time_simpl. cbn beta iota zeta. lia.
    - assert (Hwork : N.of_nat (assign_work x e (Reached m) + 1) =
        (assign_unit x e m + F.T_lin_of e + 1)%N).
      { rewrite Nat2N.inj_add, F_assign_work. cbn [ns bs ells skels labs].
        unfold assign_unit, range_payload. reflexivity. }
      rewrite Hwork. eapply N.le_trans; [apply T_assign_fast_bound|].
      apply N.mul_le_mono_l. pose proof (fast_assign_unit_le x e m). lia.
  Qed.

  Definition short_coefficients (cs : list (X.t * Z)) : Prop :=
    length cs <= 2 /\ Forall (fun p => Z.size_nat (snd p) <= 2) cs.

  Definition short_form (f : lin X.t) : Prop := short_coefficients (coef f).

  Definition shape_bits (shape : oct_shape) : nat :=
    match shape with OctConstant => 0 | OctDifference i j _ => K.bits i + K.bits j end.

  Definition coefficient_key (k : K.t) (cs : list (X.t * Z)) : Prop :=
    exists x a, fst k = x /\ In (x, a) cs.

  Definition shape_keys (shape : oct_shape) (cs : list (X.t * Z)) : Prop :=
    match shape with
    | OctConstant => True
    | OctDifference i j _ => coefficient_key i cs /\ coefficient_key j cs
    end.

  Lemma short_coefficients_nil : short_coefficients nil.
  Proof.
    split; [cbn; lia|constructor].
  Qed.

  Lemma short_coefficients_one : forall x a, Z.size_nat a <= 2 ->
    short_coefficients ((x, a) :: nil).
  Proof.
    intros x a Ha. split; [cbn; lia|]. constructor; [exact Ha|constructor].
  Qed.

  Lemma short_coefficients_two : forall x a y b,
    Z.size_nat a <= 2 -> Z.size_nat b <= 2 ->
    short_coefficients ((x, a) :: (y, b) :: nil).
  Proof.
    intros x a y b Ha Hb. split; [cbn; lia|].
    constructor; [exact Ha|]. constructor; [exact Hb|constructor].
  Qed.

  Lemma coefficient_key_member : forall cs x a k,
    fst k = x -> In (x, a) cs -> coefficient_key k cs.
  Proof.
    intros cs x a k Hkey Hin. exists x, a. now split.
  Qed.

  Lemma coefficient_key_flip : forall k cs,
    coefficient_key k cs -> coefficient_key (flip k) cs.
  Proof.
    intros k cs [x [a [Hkey Hin]]]. exists x, a. split; [|exact Hin].
    unfold flip. cbn [fst]. exact Hkey.
  Qed.

  (** Literal encodings charge twice the variable code and one sign bit. *)
  Lemma coefficient_key_bits : forall f k,
    coefficient_key k (coef f) -> K.bits k <= 2 * F.form_bits f + 1.
  Proof.
    intros f [y sign] [x [a [Hkey Hin]]]. cbn [fst] in Hkey. subst y.
    assert (Hbits : X.bits x <= F.form_bits f).
    { destruct f as [cs c]. unfold F.form_bits. cbn [coef cst] in *.
      revert Hin. induction cs as [|[z b] cs IH]; intro Hin; [contradiction|].
      cbn in Hin |- *. destruct Hin as [Heq|Hin].
      - injection Heq as Hz Hb. subst z b.
        pose proof (Nat.le_max_l (X.bits x + Z.size_nat a)
          (fold_right Nat.max (Z.size_nat c)
            (map (fun p => X.bits (fst p) + Z.size_nat (snd p)) cs))). lia.
      - eapply Nat.le_trans; [now apply IH|apply Nat.le_max_r]. }
    pose proof (signed_bits_le x sign). lia.
  Qed.

  Lemma signed_unit_shape : forall x a k, signed_unit x a = Some k ->
    Z.size_nat a <= 2 /\ fst k = x.
  Proof.
    intros x a k Hunit. unfold signed_unit in Hunit.
    destruct (a =? 1)%Z eqn:Hplus.
    - apply Z.eqb_eq in Hplus. subst a. injection Hunit as <-.
      split; [change (1 <= 2); lia|reflexivity].
    - destruct (a =? -1)%Z eqn:Hminus; [|discriminate].
      apply Z.eqb_eq in Hminus. subst a. injection Hunit as <-.
      split; [change (1 <= 2); lia|reflexivity].
  Qed.

  Lemma reverse_shape_bits : forall shape,
    shape_bits (reverse_shape shape) = shape_bits shape.
  Proof.
    intros [|i j double]; cbn [reverse_shape shape_bits]; lia.
  Qed.

  (** Accepted signed differences use at most two small coefficients and only their variables. *)
  Lemma difference_pair_shape : forall cs shape,
    difference_pair cs = Some shape ->
    short_coefficients cs /\ shape_keys shape cs.
  Proof.
    intros cs shape Hpair. destruct cs as [|[x a] cs].
    - cbn [difference_pair] in Hpair. injection Hpair as <-.
      split; [apply short_coefficients_nil|constructor].
    - destruct cs as [|[y b] cs].
      + cbn [difference_pair] in Hpair.
        destruct (signed_unit x a) as [k|] eqn:Hunit.
        * injection Hpair as <-. destruct (signed_unit_shape x a k Hunit) as [Ha Hkey].
          split; [now apply short_coefficients_one|].
          assert (Hmember : coefficient_key k ((x, a) :: nil)).
          { apply (coefficient_key_member _ x a); [exact Hkey|now left]. }
          split; [now apply coefficient_key_flip|exact Hmember].
        * destruct (a =? 2)%Z eqn:Htwo.
          -- apply Z.eqb_eq in Htwo. subst a. injection Hpair as <-.
             split; [apply short_coefficients_one; change (2 <= 2); lia|].
             split; (apply (coefficient_key_member _ x 2%Z); [reflexivity|now left]).
          -- destruct (a =? -2)%Z eqn:Hminus; [|discriminate].
             apply Z.eqb_eq in Hminus. subst a. injection Hpair as <-.
             split; [apply short_coefficients_one; change (2 <= 2); lia|].
             split; (apply (coefficient_key_member _ x (-2)%Z); [reflexivity|now left]).
      + destruct cs as [|p cs]; [|discriminate].
        cbn [difference_pair] in Hpair.
        destruct (signed_unit x a) as [i|] eqn:Hi; [|discriminate].
        destruct (signed_unit y b) as [j|] eqn:Hj; [|discriminate].
        injection Hpair as <-.
        destruct (signed_unit_shape x a i Hi) as [Ha Hix].
        destruct (signed_unit_shape y b j Hj) as [Hb Hjy].
        split; [now apply short_coefficients_two|].
        split.
        * apply coefficient_key_flip. apply (coefficient_key_member _ y b);
            [exact Hjy|right; now left].
        * apply (coefficient_key_member _ x a); [exact Hix|now left].
  Qed.

  Lemma shape_keys_bits : forall f shape, shape_keys shape (coef f) ->
    shape_bits shape <= 4 * (F.form_bits f + 1).
  Proof.
    intros f [|i j double] Hkeys; [cbn [shape_bits]; lia|].
    destruct Hkeys as [Hi Hj].
    pose proof (coefficient_key_bits f i Hi).
    pose proof (coefficient_key_bits f j Hj). cbn [shape_bits]. lia.
  Qed.

  (** Accepted atoms contain only short forms and their signed endpoint codes fit the form bits. *)
  Lemma difference_forms_shape : forall l r shape,
    difference_forms l r = Some shape ->
    short_form l /\ short_form r /\
    shape_bits shape <= 4 * (F.form_bits l + F.form_bits r + 1).
  Proof.
    intros [ls lc] [rs rc] shape Hpair.
    unfold difference_forms in Hpair. cbn [coef] in Hpair.
    destruct ls as [|[x a] ls].
    - destruct (difference_pair rs) as [found|] eqn:Hrs; [|discriminate].
      injection Hpair as <-.
      destruct (difference_pair_shape rs found Hrs) as [Hshort Hkeys].
      split; [apply short_coefficients_nil|]. split; [exact Hshort|].
      rewrite reverse_shape_bits.
      pose proof (shape_keys_bits (Lin X.t rs rc) found Hkeys). lia.
    - destruct rs as [|[y b] rs].
      + destruct (difference_pair_shape ((x, a) :: ls) shape Hpair) as [Hshort Hkeys].
        split; [exact Hshort|]. split; [apply short_coefficients_nil|].
        pose proof (shape_keys_bits (Lin X.t ((x, a) :: ls) lc) shape Hkeys). lia.
      + destruct ls as [|p ls]; [|discriminate].
        destruct rs as [|q rs]; [|discriminate].
        destruct (signed_unit x a) as [i|] eqn:Hi; [|discriminate].
        destruct (signed_unit y b) as [j|] eqn:Hj; [|discriminate].
        injection Hpair as <-.
        destruct (signed_unit_shape x a i Hi) as [Ha Hix].
        destruct (signed_unit_shape y b j Hj) as [Hb Hjy].
        split; [now apply short_coefficients_one|].
        split; [now apply short_coefficients_one|].
        assert (Hleft : coefficient_key i (coef (Lin X.t ((x, a) :: nil) lc))).
        { apply (coefficient_key_member _ x a); [exact Hix|now left]. }
        assert (Hright : coefficient_key j (coef (Lin X.t ((y, b) :: nil) rc))).
        { apply (coefficient_key_member _ y b); [exact Hjy|now left]. }
        pose proof (coefficient_key_bits (Lin X.t ((x, a) :: nil) lc) i Hleft).
        pose proof (coefficient_key_bits (Lin X.t ((y, b) :: nil) rc) j Hright).
        cbn [shape_bits]. lia.
  Qed.

  Lemma T_reverse_shape_le : forall shape, (T_reverse_shape shape <= 1)%N.
  Proof.
    intros [|i j double]; time_step.
  Qed.

  (** Probing rejects a third coefficient immediately and otherwise reads at most two integer tags. *)
  Lemma T_difference_pair_small : forall cs bits,
    Forall (fun p => Z.size_nat (snd p) <= bits) cs ->
    (T_difference_pair cs <= 256 * N.of_nat (bits + 1))%N.
  Proof.
    intros cs bits Hbits. destruct cs as [|[x a] cs]; [time_step|].
    inversion Hbits as [|p ps Ha Htail]; subst. cbn [snd] in Ha.
    destruct cs as [|[y b] cs]; [time_step|].
    inversion Htail as [|p ps Hb Hrest]; subst. cbn [snd] in Hb.
    destruct cs; time_step.
  Qed.

  Lemma T_difference_forms_small : forall l r bits,
    Forall (fun p => Z.size_nat (snd p) <= bits) (coef l) ->
    Forall (fun p => Z.size_nat (snd p) <= bits) (coef r) ->
    (T_difference_forms l r <= 1024 * N.of_nat (bits + 1))%N.
  Proof.
    intros [ls lc] [rs rc] bits Hl Hr. cbn [coef] in Hl, Hr.
    pose proof (T_difference_pair_small ls bits Hl) as Hleft.
    pose proof (T_difference_pair_small rs bits Hr) as Hright.
    destruct ls as [|[x a] ls].
    - unfold T_difference_forms. cbn beta iota zeta. time_simpl. time_cbn.
      destruct (difference_pair rs) as [found|].
      + pose proof (T_reverse_shape_le found). time_simpl. time_cbn. lia.
      + time_simpl. time_cbn. lia.
    - destruct rs as [|[y b] rs].
      + inversion Hl as [|p ps Ha Htail]; subst. cbn [snd] in Ha.
        destruct ls as [|[y b] ls]; [time_step|].
        inversion Htail as [|p ps Hb Hrest]; subst. cbn [snd] in Hb.
        destruct ls; time_step.
      + inversion Hl as [|p ps Ha Hls]; subst. cbn [snd] in Ha.
        inversion Hr as [|p ps Hb Hrs]; subst. cbn [snd] in Hb.
        destruct ls, rs; time_step.
  Qed.

  (** A recognized short form has at most three affine summands. *)
  Lemma form_fragment_short_abs : forall m f cs,
    incl cs (coef f) -> length cs <= 2 ->
    rel_bounds_abs (2 ^ (ell m + F.form_bits f + 2))
      (rel_form_bounds (variable_bounds m) (Lin X.t cs (cst f))).
  Proof.
    intros m f cs Hincl Hcount.
    eapply rel_bounds_abs_mono with
      (lower := (length cs + 1) * 2 ^ F.form_bits f * 2 ^ ell m).
    - rewrite !Nat.pow_add_r. change ((length cs + 1) * 2 ^ F.form_bits f * 2 ^ ell m <=
        (2 ^ ell m * 2 ^ F.form_bits f) * 4).
      replace ((2 ^ ell m * 2 ^ F.form_bits f) * 4) with
        ((4 * 2 ^ F.form_bits f) * 2 ^ ell m) by ring.
      apply Nat.mul_le_mono_r, Nat.mul_le_mono_r. lia.
    - apply rel_form_bounds_abs.
      + cbn [cst]. apply zbits_abs_bound, form_bits_constant.
      + cbn [coef]. apply Forall_forall. intros p Hin. apply zbits_abs_bound.
        apply form_bits_coefficient, Hincl, Hin.
      + apply variable_bounds_abs.
      + pose proof (Nat.pow_nonzero 2 (F.form_bits f) ltac:(lia)). lia.
      + pose proof (Nat.pow_nonzero 2 (ell m) ltac:(lia)). lia.
  Qed.

  (** Small coefficients make each supported assumption-form step linear in its bits. *)
  Lemma form_bounds_short_step_time : forall m f p after,
    short_form f -> In p (coef f) -> incl after (coef f) -> length after <= 2 ->
    (16 + T_variable_bounds m (fst p) +
      T_rel_scale_bounds (snd p) (variable_bounds m (fst p)) +
      T_rel_add_bounds (rel_scale_bounds (snd p) (variable_bounds m (fst p)))
        (rel_form_bounds (variable_bounds m) (Lin X.t after (cst f))) <=
      512 * (M.c_map + 1) * N.of_nat (ell m + F.form_bits f + 1))%N.
  Proof.
    intros m f p after [_ Hsmall] Hin Hincl Hcount.
    assert (Hcoefficient : Z.size_nat (snd p) <= 2).
    { apply Forall_forall with (x := p) in Hsmall; assumption. }
    assert (Hproduct : rel_bounds_abs (2 ^ (ell m + 2))
      (rel_scale_bounds (snd p) (variable_bounds m (fst p)))).
    { replace (2 ^ (ell m + 2)) with (2 ^ 2 * 2 ^ ell m)
        by (rewrite Nat.pow_add_r; ring).
      apply rel_bounds_abs_scale.
      - now apply zbits_abs_bound.
      - apply variable_bounds_abs.
      - cbn. lia.
      - pose proof (Nat.pow_nonzero 2 (ell m) ltac:(lia)). lia. }
    pose proof (form_fragment_short_abs m f after Hincl Hcount) as Hsuffix.
    pose proof (T_variable_bounds_small m (fst p)) as Hquery.
    pose proof (form_bits_key f p Hin) as Hkey.
    pose proof (rel_scale_bounds_small_time _ _ _ Hcoefficient
      (variable_bounds_abs m (fst p))) as Hscale.
    pose proof (rel_add_bounds_time _ _ _ _ Hproduct Hsuffix) as Hadd.
    set (unit := N.of_nat (ell m + F.form_bits f + 1)).
    assert (Hpositive : (1 <= unit)%N) by (unfold unit; lia).
    assert (Hquery_bits : (N.of_nat (X.bits (fst p) + ell m + 1) <= unit)%N).
    { unfold unit. apply time_of_nat_le. lia. }
    assert (Hscale_bits : (N.of_nat (ell m + 1) <= unit)%N).
    { unfold unit. apply time_of_nat_le. lia. }
    assert (Hadd_bits : (N.of_nat (ell m + 2 + (ell m + F.form_bits f + 2) + 1) <=
      5 * unit)%N).
    { unfold unit. replace (5 * N.of_nat (ell m + F.form_bits f + 1))%N with
        (N.of_nat (5 * (ell m + F.form_bits f + 1))) by
          (rewrite Nat2N.inj_mul; reflexivity).
      apply time_of_nat_le. lia. }
    assert (Hquery' : (T_variable_bounds m (fst p) <= 128 * (M.c_map + 1) * unit)%N).
    { eapply N.le_trans; [exact Hquery|]. now apply N.mul_le_mono_l. }
    assert (Hscale' : (T_rel_scale_bounds (snd p) (variable_bounds m (fst p)) <= 128 * unit)%N).
    { eapply N.le_trans; [exact Hscale|]. now apply N.mul_le_mono_l. }
    assert (Hadd' : (T_rel_add_bounds
      (rel_scale_bounds (snd p) (variable_bounds m (fst p)))
      (rel_form_bounds (variable_bounds m) (Lin X.t after (cst f))) <= 80 * unit)%N).
    { eapply N.le_trans; [exact Hadd|].
      replace (80 * unit)%N with (16 * (5 * unit))%N by ring.
      now apply N.mul_le_mono_l. }
    assert (Hcharge : (unit <= (M.c_map + 1) * unit)%N) by nia.
    replace (128 * (M.c_map + 1) * unit)%N with
      (128 * ((M.c_map + 1) * unit))%N in Hquery' by ring.
    replace (512 * (M.c_map + 1) * unit)%N with
      (512 * ((M.c_map + 1) * unit))%N by ring.
    set (charge := ((M.c_map + 1) * unit)%N) in *.
    clear Hsmall Hin Hincl Hcount Hcoefficient Hproduct Hsuffix Hquery Hkey Hscale Hadd
      Hquery_bits Hscale_bits Hadd_bits. clearbody charge unit. lia.
  Qed.

  (** The short affine fold makes at most two linear-cost steps. *)
  Lemma T_form_bounds_short : forall m f,
    short_form f ->
    (T_form_bounds m f <=
      4096 * (M.c_map + 1) * N.of_nat (ell m + F.form_bits f + 1))%N.
  Proof.
    intros m [cs c] Hshort.
    pose proof (proj1 Hshort) as Hcount. cbn [coef] in Hcount.
    time_unfold (@T_form_bounds). time_simpl. time_cbn.
    time_unfold (@T_rel_form_bounds). time_simpl. time_cbn.
    lazymatch goal with
    | |- context [Std.List.T_fold_right ?ff ?tf ?seed ?xs] =>
      assert (Hfold : (Std.List.T_fold_right ff tf seed xs <=
        (512 * ((M.c_map + 1) * N.of_nat (ell m + F.form_bits (Lin X.t cs c) + 1)) + 1) *
          N.of_nat (length xs) + 1)%N)
    end.
    { apply rel_fold_right_time. intros before p after Heq.
      assert (Hin : In p (coef (Lin X.t cs c))).
      { cbn [coef]. rewrite Heq. apply in_or_app. right. now left. }
      assert (Hincl : incl after (coef (Lin X.t cs c))).
      { intros q Hq. cbn [coef]. rewrite Heq. apply in_or_app. right. now right. }
      assert (Hafter : length after <= 2).
      { rewrite Heq, length_app in Hcount. cbn [length] in Hcount. lia. }
      pose proof (form_bounds_short_step_time m (Lin X.t cs c) p after
        Hshort Hin Hincl Hafter) as Hstep.
      unfold rel_form_bounds in Hstep. cbn [coef cst] in Hstep.
      replace (512 * (M.c_map + 1) * N.of_nat (ell m + F.form_bits (Lin X.t cs c) + 1))%N with
        (512 * ((M.c_map + 1) * N.of_nat (ell m + F.form_bits (Lin X.t cs c) + 1)))%N
        in Hstep by ring.
      eapply N.le_trans; [|exact Hstep]. time_simpl. time_cbn. lia. }
    pose proof (time_of_nat_le _ _ Hcount) as HcountN.
    change (N.of_nat (length cs) <= 2)%N in HcountN.
    set (unit := ((M.c_map + 1) * N.of_nat (ell m + F.form_bits (Lin X.t cs c) + 1))%N) in *.
    assert (Hpositive : (1 <= unit)%N) by (unfold unit; nia).
    lazymatch goal with |- (?actual <= ?rhs)%N =>
      replace rhs with (4096 * unit)%N by
        (unfold unit, F.form_bits; cbn [coef cst]; ring)
    end.
    pose proof (N.mul_le_mono_l _ _ (512 * unit + 1)%N HcountN) as Hsteps.
    replace ((512 * unit + 1) * 2)%N with (1024 * unit + 2)%N in Hsteps by ring.
    clear -Hfold Hsteps Hpositive. clearbody unit. lia.
  Qed.

  (** A supported wrap test charges the short form and its explicitly stored endpoints. *)
  Lemma T_form_exact_short : forall m f r,
    short_form f ->
    (T_form_exact m f r <= 8192 * (M.c_map + 1) *
      N.of_nat (ell m + F.form_bits f + F.wrap_bits r + 1))%N.
  Proof.
    intros m f r Hshort.
    pose proof (T_form_bounds_short m f Hshort) as Hform.
    pose proof (form_fragment_short_abs m f (coef f) (incl_refl _) (proj1 Hshort)) as Habs.
    change (rel_bounds_abs (2 ^ (ell m + F.form_bits f + 2)) (form_bounds m f)) in Habs.
    pose proof (rel_wrap_exact_time r (form_bounds m f) (F.wrap_bits r)
      (ell m + F.form_bits f + 2) (Nat.le_refl _) Habs) as Hwrap.
    clear Hshort Habs. unfold F.form_bits, F.wrap_bits in Hform, Hwrap |- *.
    unfold T_form_exact. destruct r; time_simpl; time_cbn;
      rewrite ?Nat2N.inj_add in *; nia.
  Qed.

  (** Unary signed comparisons add at most one bit when doubling their bound. *)
  Lemma scale_constraint_bits : forall double d bits,
    Z.size_nat d <= bits -> Z.size_nat (scale_constraint double d) <= bits + 1.
  Proof.
    intros [] d bits Hbits; cbn [scale_constraint]; [|lia].
    replace (2 * d)%Z with (d + d)%Z by ring. now apply zbits_add_bound.
  Qed.

  Lemma T_scale_constraint_small : forall double d,
    (T_scale_constraint double d <= 32 * N.of_nat (Z.size_nat d + 1))%N.
  Proof.
    intros double d.
    pose proof (rel_mul_small_time 2%Z d (Z.size_nat d)
      ltac:(change (2 <= 2); lia) (Nat.le_refl _)) as Hmul.
    assert (Hunit : (1 <= N.of_nat (Z.size_nat d + 1))%N) by lia.
    destruct double; time_unfold (@T_scale_constraint); time_simpl;
      cbn beta iota zeta; lia.
  Qed.

  (** A signed comparison performs at most two refinements over the same endpoint codes. *)
  Lemma grow_assume_cmp : forall shape d c s bits,
    1 <= bits -> Z.size_nat d <= bits ->
    ns (assume_cmp c shape d s) <= ns s + 8 /\
    bs (assume_cmp c shape d s) <= Nat.max (bs s) (shape_bits shape + 1) /\
    ells (assume_cmp c shape d s) <= Nat.max (ells s) (bits + 2) + 8 /\
    labs (assume_cmp c shape d s) <= labs s + 8 * (shape_bits shape + 2).
  Proof.
    intros shape d c s bits Hpositive Hbits.
    pose proof (Nat.le_max_l (bs s) (shape_bits shape + 1)) as Hbase_keys.
    pose proof (Nat.le_max_l (ells s) (bits + 2)) as Hbase_entries.
    destruct shape as [|i j double].
    - destruct c; cbn [assume_cmp shape_bits] in *;
        repeat match goal with |- context [if ?test then _ else _] => destruct test end;
        cbn [ns bs ells labs]; repeat split; lia.
    - cbn [shape_bits] in *.
      assert (Hkey_sum : Nat.max (K.bits i) (K.bits j) <= K.bits i + K.bits j).
      { apply Nat.max_lub; lia. }
      assert (Hkey_cap : Nat.max (bs s) (Nat.max (K.bits i) (K.bits j) + 1) <=
        Nat.max (bs s) (K.bits i + K.bits j + 1)).
      { apply Nat.max_lub; [apply Nat.le_max_l|].
        apply Nat.le_trans with (m := K.bits i + K.bits j + 1);
          [lia|apply Nat.le_max_r]. }
      assert (Hnormal_bits : Z.size_nat (scale_constraint double d) <= bits + 1).
      { now apply scale_constraint_bits. }
      assert (Hstrict_base : Z.size_nat (d - 1)%Z <= bits + 1).
      { change (Z.size_nat (d + (-1))%Z <= bits + 1).
        apply zbits_add_bound; [exact Hbits|]. change (1 <= bits). exact Hpositive. }
      assert (Hstrict_bits : Z.size_nat (scale_constraint double (d - 1)%Z) <= bits + 2).
      { eapply Nat.le_trans; [apply (scale_constraint_bits double (d - 1)%Z (bits + 1)
          Hstrict_base)|]. lia. }
      assert (Hnormal_cap : Nat.max (ells s) (Z.size_nat (scale_constraint double d)) <=
        Nat.max (ells s) (bits + 2)).
      { apply Nat.max_lub; [apply Nat.le_max_l|].
        apply Nat.le_trans with (m := bits + 2); [lia|apply Nat.le_max_r]. }
      destruct c; cbn [assume_cmp].
      + destruct (grow_refine i j (scale_constraint double d) s) as [Hn [Hb [He Hl]]].
        repeat split; lia.
      + destruct (grow_refine i j (scale_constraint double (d - 1)%Z) s)
          as [Hn [Hb [He Hl]]].
        assert (Hstrict_cap :
          Nat.max (ells s) (Z.size_nat (scale_constraint double (d - 1)%Z)) <=
            Nat.max (ells s) (bits + 2)).
        { apply Nat.max_lub; [apply Nat.le_max_l|].
          eapply Nat.le_trans; [exact Hstrict_bits|apply Nat.le_max_r]. }
        repeat split; lia.
      + set (next := refine i j (scale_constraint double d) s).
        destruct (grow_refine i j (scale_constraint double d) s)
          as [Hn1 [Hb1 [He1 Hl1]]].
        fold next in Hn1, Hb1, He1, Hl1.
        destruct (grow_refine j i (- scale_constraint double d)%Z next)
          as [Hn2 [Hb2 [He2 Hl2]]].
        rewrite zbits_opp in He2.
        rewrite (Nat.max_comm (K.bits j) (K.bits i)) in Hb2, Hl2.
        assert (Hkeys : Nat.max (bs next) (Nat.max (K.bits i) (K.bits j) + 1) <=
          Nat.max (bs s) (K.bits i + K.bits j + 1)).
        { apply Nat.max_lub; [lia|].
          apply Nat.le_trans with (m := K.bits i + K.bits j + 1);
            [lia|apply Nat.le_max_r]. }
        assert (Hd : Z.size_nat (scale_constraint double d) <=
          Nat.max (ells s) (bits + 2)).
        { apply Nat.le_trans with (m := bits + 2); [lia|apply Nat.le_max_r]. }
        assert (Hentries : Nat.max (ells next) (Z.size_nat (scale_constraint double d)) <=
          Nat.max (ells s) (bits + 2) + 4) by (apply Nat.max_lub; lia).
        fold next. repeat split; lia.
  Qed.

  (** Comparison dispatch, doubling and refinement fit one signed matrix allowance. *)
  Lemma T_assume_cmp_small : forall shape d c s bits,
    1 <= bits -> Z.size_nat d <= bits ->
    (T_assume_cmp c shape d s <= 1024 * c_octagon * N.of_nat
      ((ns s + 1)^2 * (bs s + ells s + shape_bits shape + bits + 1) + labs s))%N.
  Proof.
    intros [|i j double] d c s bits Hpositive Hbits.
    - set (units := (ns s + 1)^2 * (bs s + ells s + 0 + bits + 1) + labs s).
      assert (Hpayload : bs s + ells s + bits + 1 <= units).
      { pose proof (quadratic_payload_le (ns s) (bs s + ells s + bits + 1)).
        unfold units. lia. }
      assert (Hscalar : Z.size_nat d + 1 <= units) by lia.
      pose proof (time_of_nat_le _ _ Hscalar) as Hscalar_cast.
      pose proof (time_of_nat_le 1 units ltac:(lia)) as Hwork.
      set (work := N.of_nat units) in *.
      change (1 <= work)%N in Hwork.
      assert (Htest : (T_assume_cmp c OctConstant d s <= 32 * work)%N).
      { destruct c; time_unfold (@T_assume_cmp); time_simpl; time_step. }
      change (T_assume_cmp c OctConstant d s <= 1024 * c_octagon * work)%N.
      eapply N.le_trans; [exact Htest|]. apply N.mul_le_mono_r.
      pose proof (N.le_0_l M.c_map) as Hmap. clear -Hmap. unfold c_octagon. nia.
    - set (units := (ns s + 1)^2 *
        (bs s + ells s + K.bits i + K.bits j + bits + 1) + labs s).
      cbn [shape_bits].
      replace (bs s + ells s + (K.bits i + K.bits j) + bits + 1) with
        (bs s + ells s + K.bits i + K.bits j + bits + 1) by lia.
      change (T_assume_cmp c (OctDifference i j double) d s <=
        1024 * c_octagon * N.of_nat units)%N.
      assert (Hpayload : bs s + ells s + K.bits i + K.bits j + bits + 1 <= units).
      { pose proof (quadratic_payload_le (ns s)
          (bs s + ells s + K.bits i + K.bits j + bits + 1)).
        unfold units. lia. }
      assert (Hunit : 1 <= units) by lia.
      assert (Hscalar : Z.size_nat d + 1 <= units) by lia.
      assert (Hstrict_bits : Z.size_nat (d - 1)%Z <= bits + 1).
      { change (Z.size_nat (d + (-1))%Z <= bits + 1).
        apply zbits_add_bound; [exact Hbits|]. change (1 <= bits). exact Hpositive. }
      assert (Hnormal_bits : Z.size_nat (scale_constraint double d) <= bits + 2).
      { pose proof (scale_constraint_bits double d bits Hbits). lia. }
      assert (Hscaled_strict_bits :
        Z.size_nat (scale_constraint double (d - 1)%Z) <= bits + 2).
      { pose proof (scale_constraint_bits double (d - 1)%Z (bits + 1) Hstrict_bits). lia. }
      assert (Hwide_units : (ns s + 1)^2 *
        (bs s + ells s + K.bits i + K.bits j + (bits + 2) + 1) + labs s <= 3 * units).
      { unfold units. replace (3 * ((ns s + 1)^2 *
          (bs s + ells s + K.bits i + K.bits j + bits + 1) + labs s)) with
          ((ns s + 1)^2 *
            (3 * (bs s + ells s + K.bits i + K.bits j + bits + 1)) + 3 * labs s) by ring.
        apply Nat.add_le_mono; [apply Nat.mul_le_mono_l; lia|lia]. }
      assert (Hsingle_units : forall v, Z.size_nat v <= bits + 2 ->
        (ns s + 1)^2 *
          (bs s + K.bits i + K.bits j + ells s + Z.size_nat v + 1) + labs s <= 3 * units).
      { intros v Hv. eapply Nat.le_trans; [|exact Hwide_units].
        apply Nat.add_le_mono_r, Nat.mul_le_mono_l. lia. }
      assert (Hstrict_scalar : Z.size_nat (d - 1)%Z + 1 <= 2 * units) by lia.
      pose proof (time_of_nat_le _ _ Hwide_units) as Hwide_cast.
      pose proof (time_of_nat_le _ _ Hscalar) as Hscalar_cast.
      pose proof (time_of_nat_le _ _ Hstrict_scalar) as Hstrict_scalar_cast.
      rewrite (Nat2N.inj_mul 3 units) in Hwide_cast.
      rewrite (Nat2N.inj_mul 2 units) in Hstrict_scalar_cast.
      pose proof (time_of_nat_le _ _ Hunit) as Hwork.
      set (work := N.of_nat units) in *.
      change (1 <= work)%N in Hwork.
      set (charge := (c_octagon * work)%N).
      assert (Hsingle : forall v, Z.size_nat v <= bits + 2 ->
        (T_refine i j v s <= 1 + 3 * charge)%N).
      { intros v Hv. pose proof (time_of_nat_le _ _ (Hsingle_units v Hv)) as Hcast.
        rewrite (Nat2N.inj_mul 3 units) in Hcast. fold work in Hcast.
        eapply N.le_trans; [apply T_refine_small|].
        replace (3 * charge)%N with (c_octagon * (3 * work))%N by (unfold charge; ring).
        apply N.add_le_mono_l, N.mul_le_mono_l. exact Hcast. }
      pose proof (Hsingle (scale_constraint double d) Hnormal_bits) as Hnormal.
      pose proof (Hsingle (scale_constraint double (d - 1)%Z) Hscaled_strict_bits) as Hstrict.
      assert (Hopp_bits : Z.size_nat (- scale_constraint double d)%Z <= bits + 2)
        by (now rewrite zbits_opp).
      pose proof (T_refine_pair_small i j (scale_constraint double d)
        (- scale_constraint double d)%Z s (bits + 2) Hnormal_bits Hopp_bits) as Hpair_raw.
      assert (Hpair : (T_refine i j (scale_constraint double d) s +
        T_refine j i (- scale_constraint double d)%Z
          (refine i j (scale_constraint double d) s) <= 768 * charge)%N).
      { eapply N.le_trans; [exact Hpair_raw|].
        replace (768 * charge)%N with (256 * c_octagon * (3 * work))%N
          by (unfold charge; ring).
        now apply N.mul_le_mono_l. }
      assert (Hscale : (T_scale_constraint double d <= 32 * work)%N).
      { eapply N.le_trans; [apply T_scale_constraint_small|].
        now apply N.mul_le_mono_l. }
      assert (Hstrict_scale : (T_scale_constraint double (d - 1)%Z <= 64 * work)%N).
      { eapply N.le_trans; [apply T_scale_constraint_small|].
        replace (64 * work)%N with (32 * (2 * work))%N by ring.
        now apply N.mul_le_mono_l. }
      pose proof (Z.T_sub_le d 1%Z) as Hsub_raw.
      change (Z.size_nat 1%Z) with 1%nat in Hsub_raw.
      assert (Hsub : (Z.T_sub d 1%Z <= 6 * work)%N).
      { pose proof (N.mul_le_mono_l _ _ 3%N Hscalar_cast) as Hscaled. lia. }
      pose proof (Z.T_opp_le (scale_constraint double d)) as Hopp.
      assert (Hcoefficient : (1 <= c_octagon)%N).
      { pose proof (N.le_0_l M.c_map) as Hmap. clear -Hmap. unfold c_octagon. nia. }
      assert (Hwork_charge : (work <= charge)%N).
      { unfold charge. replace work with (1 * work)%N at 1 by ring.
        now apply N.mul_le_mono_r. }
      assert (Hcharge : (1 <= charge)%N) by lia.
      replace (1024 * c_octagon * work)%N with (1024 * charge)%N
        by (unfold charge; ring).
      destruct c; unfold T_assume_cmp; cbn beta iota zeta; time_simpl;
        clearbody charge work;
        clear -Hnormal Hstrict Hpair Hscale Hstrict_scale Hsub Hopp Hcharge Hwork_charge; lia.
  Qed.

  (** Atom size includes both affine forms and both stored wrap endpoints. *)
  Definition assume_atom_bits (a : atom X.t) : nat :=
    F.form_bits (al a) + F.wrap_bits (alw a) +
      F.form_bits (ar a) + F.wrap_bits (arw a).

  (** The comparison constant is the difference of the two affine seeds. *)
  Lemma assume_difference_bits : forall l r,
    Z.size_nat (cst r - cst l)%Z <= F.form_bits l + F.form_bits r + 1.
  Proof.
    intros l r. change (Z.size_nat (cst r + (-cst l))%Z <=
      F.form_bits l + F.form_bits r + 1).
    apply zbits_add_bound.
    - pose proof (form_bits_constant r). lia.
    - rewrite zbits_opp. pose proof (form_bits_constant l). lia.
  Qed.

  (** A recognized atom bounds its signed endpoints by the two source forms. *)
  Lemma grow_assume_atom : forall s a B,
    assume_atom_bits a <= B ->
    ns (assume_atom s a) <= ns s + 8 /\
    bs (assume_atom s a) <= Nat.max (bs s) (4 * B + 5) /\
    ells (assume_atom s a) <= Nat.max (ells s) (B + 3) + 8 /\
    labs (assume_atom s a) <= labs s + 48 * (B + 1).
  Proof.
    intros [|m] a B Hbits.
    - cbn [assume_atom ns bs ells labs]. repeat split; lia.
    - assert (Hsame : ns (Reached m) <= ns (Reached m) + 8 /\
        bs (Reached m) <= Nat.max (bs (Reached m)) (4 * B + 5) /\
        ells (Reached m) <= Nat.max (ells (Reached m)) (B + 3) + 8 /\
        labs (Reached m) <= labs (Reached m) + 48 * (B + 1)).
      { pose proof (Nat.le_max_l (bs (Reached m)) (4 * B + 5)).
        pose proof (Nat.le_max_l (ells (Reached m)) (B + 3)).
        repeat split; lia. }
      cbn [assume_atom].
      destruct (difference_forms (al a) (ar a)) as [shape|] eqn:Hforms; [|exact Hsame].
      destruct (andb (form_exact m (al a) (alw a))
        (form_exact m (ar a) (arw a))); [|exact Hsame].
      destruct (difference_forms_shape (al a) (ar a) shape Hforms)
        as [Hl [Hr Hkeys]].
      pose proof (assume_difference_bits (al a) (ar a)) as Hdifference.
      unfold assume_atom_bits in Hbits.
      assert (Hscalar : Z.size_nat (cst (ar a) - cst (al a))%Z <= B + 1) by lia.
      destruct (grow_assume_cmp shape (cst (ar a) - cst (al a))%Z
        (acmp a) (Reached m) (B + 1) ltac:(lia) Hscalar) as [Hn [Hb [He Hlabels]]].
      assert (Hkey_cap : shape_bits shape + 1 <= 4 * B + 5) by lia.
      assert (Hkeys_max : Nat.max (bs (Reached m)) (shape_bits shape + 1) <=
        Nat.max (bs (Reached m)) (4 * B + 5)).
      { apply Nat.max_lub; [apply Nat.le_max_l|].
        eapply Nat.le_trans; [exact Hkey_cap|apply Nat.le_max_r]. }
      assert (Hlabel_cap : 8 * (shape_bits shape + 2) <= 48 * (B + 1)) by lia.
      replace (B + 1 + 2) with (B + 3) in He by lia.
      repeat split; lia.
  Qed.

  (** Atom clocks combine short-form exactness checks with the signed comparison update. *)
  Lemma T_assume_atom_small : forall s a B,
    assume_atom_bits a <= B ->
    (T_assume_atom s a <= 8192 * c_octagon * N.of_nat
      ((ns s + 1)^2 * (bs s + ells s + B + 1) + labs s))%N.
  Proof.
    intros [|m] [l lw c r rw] B Hbits.
    - change (1 <= 8192 * c_octagon *
        N.of_nat ((0 + 1)^2 * (0 + 0 + B + 1) + 0))%N.
      replace ((0 + 1)^2 * (0 + 0 + B + 1) + 0) with (B + 1)
        by (cbn [Nat.pow]; ring).
      pose proof (time_of_nat_le 1 (B + 1) ltac:(lia)) as Hwork.
      change (1 <= N.of_nat (B + 1))%N in Hwork.
      assert (Hcoefficient : (1 <= 8192 * c_octagon)%N) by (unfold c_octagon; nia).
      eapply N.le_trans; [exact Hwork|].
      replace (N.of_nat (B + 1)) with (1 * N.of_nat (B + 1))%N at 1 by ring.
      now apply N.mul_le_mono_r.
    - unfold assume_atom_bits in Hbits. cbn [al alw ar arw] in Hbits.
      set (units := (supp m + 1)^2 * (b m + ell m + B + 1) + M.weight m).
      change (T_assume_atom (Reached m) (Atom X.t l lw c r rw) <=
        8192 * c_octagon * N.of_nat units)%N.
      assert (Hpayload : b m + ell m + B + 1 <= units).
      { pose proof (quadratic_payload_le (supp m) (b m + ell m + B + 1)).
        unfold units. lia. }
      assert (Hunit : 1 <= units) by lia.
      assert (Hscalar_unit : B + 1 <= units) by lia.
      assert (Hlcoef : Forall (fun p => Z.size_nat (snd p) <= B) (coef l)).
      { apply Forall_forall. intros p Hp.
        pose proof (form_bits_coefficient l p Hp). lia. }
      assert (Hrcoef : Forall (fun p => Z.size_nat (snd p) <= B) (coef r)).
      { apply Forall_forall. intros p Hp.
        pose proof (form_bits_coefficient r p Hp). lia. }
      pose proof (T_difference_forms_small l r B Hlcoef Hrcoef) as Hprobe_raw.
      pose proof (time_of_nat_le _ _ Hscalar_unit) as Hscalar_cast.
      pose proof (time_of_nat_le _ _ Hunit) as Hwork.
      set (work := N.of_nat units) in *.
      change (1 <= work)%N in Hwork.
      set (charge := (c_octagon * work)%N).
      set (map_charge := ((M.c_map + 1) * work)%N).
      assert (Hprobe : (T_difference_forms l r <= 1024 * work)%N).
      { eapply N.le_trans; [exact Hprobe_raw|].
        apply N.mul_le_mono_l. exact Hscalar_cast. }
      assert (Hcoefficient :
        (6144 * c_octagon + 16384 * (M.c_map + 1) + 1024 + 6 + 32 <=
          8192 * c_octagon)%N).
      { pose proof (N.le_0_l M.c_map) as Hmap. clear -Hmap. unfold c_octagon. nia. }
      pose proof (N.mul_le_mono_r _ _ work Hcoefficient) as Hbudget.
      replace ((6144 * c_octagon + 16384 * (M.c_map + 1) + 1024 + 6 + 32) * work)%N with
        (6144 * charge + 16384 * map_charge + 1024 * work + 6 * work + 32 * work)%N
        in Hbudget by (unfold charge, map_charge; ring).
      replace (8192 * c_octagon * work)%N with (8192 * charge)%N in Hbudget |- *
        by (unfold charge; ring).
      destruct (difference_forms l r) as [shape|] eqn:Hforms.
      + destruct (difference_forms_shape l r shape Hforms) as [Hl [Hr Hkeys]].
        pose proof (form_bits_constant l) as Hconstant_l.
        pose proof (form_bits_constant r) as Hconstant_r.
        pose proof (assume_difference_bits l r) as Hsub_bits.
        assert (Hscalar : Z.size_nat (cst r - cst l)%Z <= B + 1) by lia.
        assert (Hkeys_cap : shape_bits shape <= 4 * (B + 1)) by lia.
        assert (Hcmp_units : (supp m + 1)^2 *
          (b m + ell m + shape_bits shape + (B + 1) + 1) + M.weight m <= 6 * units).
        { unfold units. replace
            (6 * ((supp m + 1)^2 * (b m + ell m + B + 1) + M.weight m)) with
            ((supp m + 1)^2 * (6 * (b m + ell m + B + 1)) + 6 * M.weight m) by ring.
          apply Nat.add_le_mono; [apply Nat.mul_le_mono_l; lia|lia]. }
        pose proof (time_of_nat_le _ _ Hcmp_units) as Hcmp_cast.
        rewrite (Nat2N.inj_mul 6 units) in Hcmp_cast. fold work in Hcmp_cast.
        assert (Hcmp : (T_assume_cmp c shape (cst r - cst l)%Z (Reached m) <=
          6144 * charge)%N).
        { eapply N.le_trans.
          - exact (T_assume_cmp_small shape (cst r - cst l)%Z c (Reached m)
              (B + 1) ltac:(lia) Hscalar).
          - replace (6144 * charge)%N with (1024 * c_octagon * (6 * work))%N
              by (unfold charge; ring).
            apply N.mul_le_mono_l. exact Hcmp_cast. }
        assert (Hleft_units : ell m + F.form_bits l + F.wrap_bits lw + 1 <= units) by lia.
        assert (Hright_units : ell m + F.form_bits r + F.wrap_bits rw + 1 <= units) by lia.
        assert (Hleft : (T_form_exact m l lw <= 8192 * map_charge)%N).
        { eapply N.le_trans; [exact (T_form_exact_short m l lw Hl)|].
          replace (8192 * map_charge)%N with
            (8192 * (M.c_map + 1) * work)%N by (unfold map_charge; ring).
          apply N.mul_le_mono_l. exact (time_of_nat_le _ _ Hleft_units). }
        assert (Hright : (T_form_exact m r rw <= 8192 * map_charge)%N).
        { eapply N.le_trans; [exact (T_form_exact_short m r rw Hr)|].
          replace (8192 * map_charge)%N with
            (8192 * (M.c_map + 1) * work)%N by (unfold map_charge; ring).
          apply N.mul_le_mono_l. exact (time_of_nat_le _ _ Hright_units). }
        pose proof (Z.T_sub_le (cst r) (cst l)) as Hsub_raw.
        assert (Hsub_units : Z.size_nat (cst r) + Z.size_nat (cst l) <= units) by lia.
        pose proof (time_of_nat_le _ _ Hsub_units) as Hsub_cast. fold work in Hsub_cast.
        assert (Hsub : (Z.T_sub (cst r) (cst l) <= 6 * work)%N).
        { pose proof (N.mul_le_mono_l _ _ 3%N Hsub_cast). lia. }
        pose proof (Std.Datatypes.T_andb_le (form_exact m l lw) (form_exact m r rw)) as Hbool.
        unfold T_assume_atom. cbn beta iota zeta. cbn [al alw acmp ar arw].
        rewrite Hforms. cbn beta iota zeta.
        destruct (andb (form_exact m l lw) (form_exact m r rw));
          time_simpl; time_cbn;
          clearbody charge map_charge work;
          clear -Hprobe Hleft Hright Hcmp Hsub Hbool Hbudget Hwork; lia.
      + unfold T_assume_atom. cbn beta iota zeta. cbn [al alw acmp ar arw].
        rewrite Hforms. cbn beta iota zeta. time_simpl. time_cbn.
        clearbody charge map_charge work. clear -Hprobe Hbudget Hwork. lia.
  Qed.

  (** Signed assumptions accumulate support, entry-bit and raw-label allowances. *)

Definition assume_grid_work (initial : t) (bits count : nat) : nat :=
    (ns initial + 2 * count + 1)^2 *
      (bs initial + ells initial + bits + 2 * count + 1).

  Definition assume_stage (initial : t) (bits index : nat) (state : t) : Prop :=
    ns state <= ns initial + 8 * index /\
    bs state <= bs initial + 4 * bits + 5 /\
    ells state <= ells initial + bits + 3 + 8 * index /\
    labs state <= labs initial + 48 * index * (bits + 1).

  Lemma assume_grid_positive : forall initial bits count,
    1 <= assume_grid_work initial bits count.
  Proof.
    intros initial bits count. unfold assume_grid_work.
    eapply Nat.le_trans; [|apply quadratic_payload_le]. lia.
  Qed.

  Lemma assume_stage_initial : forall initial bits,
    assume_stage initial bits 0 initial.
  Proof.
    intros initial bits. unfold assume_stage. repeat split; lia.
  Qed.

  Lemma assume_stage_step : forall initial bits index state item,
    assume_stage initial bits index state -> assume_atom_bits item <= bits ->
    assume_stage initial bits (S index) (assume_atom state item).
  Proof.
    intros initial bits index state item [Hn [Hb [He Hl]]] Hitem.
    destruct (grow_assume_atom state item bits Hitem) as [Hn' [Hb' [He' Hl']]].
    assert (Hmaxb : Nat.max (bs state) (4 * bits + 5) <=
      bs initial + 4 * bits + 5) by (apply Nat.max_lub; lia).
    assert (Hmaxe : Nat.max (ells state) (bits + 3) <=
      ells initial + bits + 3 + 8 * index) by (apply Nat.max_lub; lia).
    unfold assume_stage. repeat split; nia.
  Qed.

  Lemma assume_stage_work : forall initial bits count index state,
    index < count -> assume_stage initial bits index state ->
    (ns state + 1)^2 * (bs state + ells state + bits + 1) + labs state <=
      192 * (assume_grid_work initial bits count + labs initial).
  Proof.
    intros initial bits count index state Hindex [Hn [Hb [He Hl]]].
    assert (Hwidth : ns state + 1 <= 4 * (ns initial + 2 * count + 1)) by lia.
    assert (Hpayload : bs state + ells state + bits + 1 <=
      9 * (bs initial + ells initial + bits + 2 * count + 1)) by lia.
    assert (Hmatrix : (ns state + 1)^2 * (bs state + ells state + bits + 1) <=
      144 * assume_grid_work initial bits count).
    { replace (144 * assume_grid_work initial bits count) with
        ((4 * (ns initial + 2 * count + 1))^2 *
          (9 * (bs initial + ells initial + bits + 2 * count + 1)))
        by (unfold assume_grid_work; cbn [Nat.pow]; ring).
      apply Nat.mul_le_mono; [now apply Nat.pow_le_mono_l|exact Hpayload]. }
    assert (Hsquare : index <= (ns initial + 2 * count + 1)^2).
    { cbn [Nat.pow]. nia. }
    assert (Hlabels : index * (bits + 1) <= assume_grid_work initial bits count).
    { unfold assume_grid_work. apply Nat.mul_le_mono; [exact Hsquare|lia]. }
    set (work := assume_grid_work initial bits count) in *.
    clearbody work. nia.
  Qed.

  Lemma T_assume_fold_stages : forall initial bits xs,
    Forall (fun item => assume_atom_bits item <= bits) xs ->
    (Std.List.T_fold_left assume_atom (fun state item => T_assume_atom state item)
      xs initial <=
      (2097152 * c_octagon *
        N.of_nat (assume_grid_work initial bits (length xs) + labs initial) + 1) *
        N.of_nat (length xs) + 1)%N.
  Proof.
    intros initial bits xs Hgood.
    assert (Htime : forall index state item, index < length xs ->
      assume_stage initial bits index state -> assume_atom_bits item <= bits ->
      (T_assume_atom state item <= 2097152 * c_octagon *
        N.of_nat (assume_grid_work initial bits (length xs) + labs initial))%N).
    { intros index state item Hindex Hstate Hitem.
      pose proof (T_assume_atom_small state item bits Hitem) as Hatom.
      pose proof (assume_stage_work initial bits (length xs) index state Hindex Hstate)
        as Hstage.
      assert (Hstage' : (ns state + 1)^2 *
        (bs state + ells state + bits + 1) + labs state <=
        256 * (assume_grid_work initial bits (length xs) + labs initial)).
      { eapply Nat.le_trans; [exact Hstage|]. apply Nat.mul_le_mono_r. lia. }
      pose proof (time_of_nat_le _ _ Hstage') as Hcast.
      rewrite (Nat2N.inj_mul 256
        (assume_grid_work initial bits (length xs) + labs initial)) in Hcast.
      eapply N.le_trans; [exact Hatom|].
      replace (2097152 * c_octagon * N.of_nat
        (assume_grid_work initial bits (length xs) + labs initial))%N with
        (8192 * c_octagon * (256 * N.of_nat
          (assume_grid_work initial bits (length xs) + labs initial)))%N by ring.
      apply N.mul_le_mono_l. exact Hcast. }
    exact (rel_fold_left_time_stages t (atom X.t) assume_atom
      (fun state item => T_assume_atom state item) (assume_stage initial bits)
      (fun item => assume_atom_bits item <= bits) (length xs)
      (2097152 * c_octagon *
        N.of_nat (assume_grid_work initial bits (length xs) + labs initial))%N
      (assume_stage_step initial bits) Htime xs Hgood 0 initial
      ltac:(lia) (assume_stage_initial initial bits)).
  Qed.

  Lemma assume_work_grid : forall g es initial,
    assume_work g es initial =
      length (F.atoms_of g es) *
        (assume_grid_work initial (F.bits_es g es) (length (F.atoms_of g es)) +
          labs initial) + N.to_nat (F.T_atoms_of g es).
  Proof.
    intros g es initial. unfold assume_work, assume_grid_work. ring.
  Qed.

  Lemma T_assume_overhead : forall g es initial,
    (T_assume g es initial <= F.T_atoms_of g es +
      Std.List.T_fold_left assume_atom (fun state item => T_assume_atom state item)
        (F.atoms_of g es) initial + 1)%N.
  Proof.
    intros g es [|m]; unfold T_assume; cbn beta iota zeta; lia.
  Qed.

  Lemma assume_time_coefficient : (4194304 * c_octagon <= c_num)%N.
  Proof.
    unfold c_octagon, c_num. nia.
  Qed.

  Lemma T_assume_le : forall g es initial,
    (T_assume g es initial <= c_num * N.of_nat (assume_work g es initial + 1))%N.
  Proof.
    intros g es initial.
    assert (Hgood : Forall
      (fun item => assume_atom_bits item <= F.bits_es g es) (F.atoms_of g es)).
    { pose proof (proj2 (F.atoms_of_size g es)) as Hatoms.
      eapply Forall_impl; [|exact Hatoms].
      intros item Hitem. unfold assume_atom_bits. exact (proj2 Hitem). }
    pose proof (T_assume_fold_stages initial (F.bits_es g es) (F.atoms_of g es)
      Hgood) as Hfold.
    pose proof (T_assume_overhead g es initial) as Hoverhead.
    rewrite assume_work_grid.
    repeat rewrite Nat2N.inj_add.
    rewrite Nat2N.inj_mul, N2Nat.id.
    eapply N.le_trans with
      (F.T_atoms_of g es +
        (2097152 * c_octagon * N.of_nat
          (assume_grid_work initial (F.bits_es g es) (length (F.atoms_of g es)) +
            labs initial) + 1) *
        N.of_nat (length (F.atoms_of g es)) + 2)%N.
    - lia.
    - apply rel_fold_overhead_budget.
      + unfold c_octagon. nia.
      + apply (time_of_nat_le 1%nat _).
        pose proof (assume_grid_positive initial (F.bits_es g es)
          (length (F.atoms_of g es))). lia.
      + pose proof assume_time_coefficient. nia.
  Qed.

  (** Assignment is linear in the numeric work charged by its contract. *)
  Lemma assign_bigO : bigO (fun _ : X.t * term L.op X.t * t => True)
    (fun x => N.of_nat (assign_work (fst (fst x)) (snd (fst x)) (snd x)))
    (fun x => T_assign (fst (fst x)) (snd (fst x)) (snd x)).
  Proof.
    apply bigO_intro with (c := c_num). intros [[x e] s] _.
    cbn [fst snd]. pose proof (T_assign_le x e s) as Htime.
    rewrite Nat2N.inj_add in Htime. cbn [N.of_nat] in Htime. nia.
  Qed.

  (** Havoc is linear in the numeric work charged by its contract. *)
  Lemma havoc_bigO : bigO (fun _ : X.t * t => True)
    (fun x => N.of_nat (havoc_work (fst x) (snd x)))
    (fun x => T_havoc (fst x) (snd x)).
  Proof.
    apply bigO_intro with (c := c_num). intros [x s] _.
    cbn [fst snd]. pose proof (T_havoc_le x s) as Htime.
    rewrite Nat2N.inj_add in Htime. cbn [N.of_nat] in Htime. nia.
  Qed.

  (** Assumption is linear in the numeric work charged by its contract. *)
  Lemma assume_bigO : bigO (fun _ : L.guard * list (term L.op X.t) * t => True)
    (fun x => N.of_nat (assume_work (fst (fst x)) (snd (fst x)) (snd x)))
    (fun x => T_assume (fst (fst x)) (snd (fst x)) (snd x)).
  Proof.
    apply bigO_intro with (c := c_num). intros [[g es] s] _.
    cbn [fst snd]. pose proof (T_assume_le g es s) as Htime.
    rewrite Nat2N.inj_add in Htime. cbn [N.of_nat] in Htime. nia.
  Qed.

  (** A range query is linear in the numeric work charged by its contract. *)
  Lemma range_bigO : bigO (fun _ : term L.op X.t * t => True)
    (fun x => N.of_nat (range_work (fst x) (snd x)))
    (fun x => T_range (fst x) (snd x)).
  Proof.
    apply bigO_intro with (c := c_num). intros [e s] _.
    cbn [fst snd]. pose proof (T_range_le e s) as Htime.
    rewrite Nat2N.inj_add in Htime. cbn [N.of_nat] in Htime. nia.
  Qed.

  (** Tight closure is cubic in the support with a linear bit-width factor. *)
  Lemma tclose_bigO : bigO (fun m : dbm => dbm_wf m)
    (fun m => N.of_nat ((supp m + 1)^3 * (b m + ell m + Nat.log2 (supp m) + 1)))
    (fun m => T_tclose m).
  Proof.
    apply bigO_intro with (c := c_octagon). intros m Hwf.
    pose proof (T_tclose_le m Hwf) as Htime. rewrite Nat2N.inj_mul. nia.
  Qed.

  (** Incremental closure is quadratic in the support and also scans the outer labels. *)
  Lemma incr_close_bigO : bigO (fun x : K.t * K.t * Z * dbm => dbm_wf (snd x))
    (fun x => N.of_nat ((supp (snd x) + 1)^2 *
      (b (snd x) + K.bits (fst (fst (fst x))) + K.bits (snd (fst (fst x))) +
        ell (snd x) + Z.size_nat (snd (fst x)) + 1) + M.weight (snd x)))
    (fun x => T_incr_close (fst (fst (fst x))) (snd (fst (fst x))) (snd (fst x)) (snd x)).
  Proof.
    apply bigO_intro with (c := c_octagon). intros [[[i j] d] m] _.
    cbn [fst snd]. pose proof (T_incr_close_le i j d m) as Htime.
    rewrite Nat2N.inj_add, Nat2N.inj_mul. nia.
  Qed.

  (** Inclusion is linear in sparse structure and stored entries times their bit width. *)
  Lemma leb_bigO : bigO (fun _ : t * t => True)
    (fun x => N.of_nat ((skels (fst x) + skels (snd x) + entries (fst x) + entries (snd x) +
        labs (fst x) + labs (snd x) + 1) *
      (bs (fst x) + bs (snd x) + ells (fst x) + ells (snd x) + 1)))
    (fun x => T_leb (fst x) (snd x)).
  Proof.
    apply bigO_intro with (c := matrix_time_factor). intros [a b] _.
    cbn [fst snd]. pose proof (T_leb_entries_le a b) as Htime.
    unfold lattice_work in Htime. lia.
  Qed.

  (** Join is linear in sparse structure and stored entries times their bit width. *)
  Lemma join_bigO : bigO (fun _ : t * t => True)
    (fun x => N.of_nat ((skels (fst x) + skels (snd x) + entries (fst x) + entries (snd x) +
        labs (fst x) + labs (snd x) + 1) *
      (bs (fst x) + bs (snd x) + ells (fst x) + ells (snd x) + 1)))
    (fun x => T_join (fst x) (snd x)).
  Proof.
    apply bigO_intro with (c := matrix_time_factor). intros [a b] _.
    cbn [fst snd]. pose proof (T_join_entries_le a b) as Htime.
    unfold lattice_work in Htime. lia.
  Qed.

  (** Widening is linear in sparse structure and stored entries times their bit width. *)
  Lemma widen_bigO : bigO (fun _ : wparam * t * t => True)
    (fun x => N.of_nat ((skels (snd (fst x)) + skels (snd x) +
        entries (snd (fst x)) + entries (snd x) + labs (snd (fst x)) + labs (snd x) + 1) *
      (bs (snd (fst x)) + bs (snd x) + ells (snd (fst x)) + ells (snd x) + 1)))
    (fun x => T_widen (fst (fst x)) (snd (fst x)) (snd x)).
  Proof.
    apply bigO_intro with (c := c_lat). intros [[p a] b] _.
    cbn [fst snd]. pose proof (T_widen_entries_le p a b) as Htime.
    unfold lattice_work in Htime. lia.
  Qed.

  Lemma assign_fast_bigO : bigO (fun _ : X.t * term L.op X.t * t => True)
    (fun x => (N.of_nat (skels (snd x) +
      (ns (snd x) + 1) * (bs (snd x) + ells (snd x) + X.bits (fst (fst x)) +
        F.bits_e (snd (fst x)) + lin_bits (snd (fst x)) + 1) +
      (tsize (snd (fst x)) + 1) * (bs (snd x) + ells (snd x) + F.bits_e (snd (fst x)) +
        Nat.log2 (tsize (snd (fst x))) + 1)^2 + labs (snd x)) +
      F.T_lin_of (snd (fst x)))%N)
    (fun x => T_assign (fst (fst x)) (snd (fst x)) (snd x)).
  Proof. Admitted. (* STUB *)
End OctagonT.
