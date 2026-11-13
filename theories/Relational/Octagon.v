(** * Integer octagons

    Sparse signed difference matrices support entrywise lattice operations.
    For example, joining upper bounds 3 and 5 retains the weaker bound 5.
    Builds on: OctagonSig, keyed map laws and numeric linearization. *)

From Stdlib Require Import List Bool ZArith NArith Lia.
From Argent Require Import Time Tactics Std.
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
          if andb (copy_allowed x source) (rel_wrap_exact r bounds) then
            assign_copy x source (cst f) s
          else add_range x (rel_wrap_bounds r bounds) (havoc x s)
        | None => add_range x (rel_wrap_bounds r bounds) (havoc x s)
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
    - destruct (andb (copy_allowed x source) (rel_wrap_exact r (form_bounds m f))) eqn:Hexact.
      + apply andb_true_iff in Hexact. destruct Hexact as [Hallowed Hwrap].
        apply assign_copy_sound; [exact Hallowed|exact Hmodel|].
        rewrite Hvalue, (rel_wrap_exact_sound r (form_bounds m f) _ Hbounds Hwrap).
        now apply copy_source_sound.
      + apply add_range_sound; [now apply havoc_sound|]. now rewrite Hupdate.
    - apply add_range_sound; [now apply havoc_sound|]. now rewrite Hupdate.
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
    (1048576 * (M.c_map + K.c_key + X.c_key + 1) *
      (M.c_map + K.c_key + X.c_key + 1))%N.
  Lemma T_assign_le : forall x e s,
    (T_assign x e s <= c_num * N.of_nat (assign_work x e s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_havoc_le : forall x s,
    (T_havoc x s <= c_num * N.of_nat (havoc_work x s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_assume_le : forall g es s,
    (T_assume g es s <= c_num * N.of_nat (assume_work g es s + 1))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_range_le : forall e s, (T_range e s <= c_num * N.of_nat (range_work e s + 1))%N.
  Proof. Admitted. (* STUB *)
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

  Definition c_octagon : N := (65536 * (M.c_map + 1) * (M.c_map + 1))%N.

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
  Lemma T_tclose_le : forall m, dbm_wf m ->
    (T_tclose m <= c_octagon * N.of_nat (((supp m + 1)^3)%nat) *
    N.of_nat ((b m + ell m + Nat.log2 (supp m) + 1)%nat))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_incr_close_le : forall i j d m, (T_incr_close i j d m <=
    c_octagon * N.of_nat (((supp m + 1)^2)%nat) *
      N.of_nat ((b m + K.bits i + K.bits j + ell m + Z.size_nat d + 1)%nat) +
    c_octagon * N.of_nat (M.weight m))%N.
  Proof. Admitted. (* STUB *)
  Definition coherent (m : dbm) : Prop :=
    forall i j, entry m i j = entry m (bar j) (bar i).
  Definition coh (s : t) : Prop :=
    match s with Unreached => True | Reached m => coherent m end.
  Definition same_entries (a b : t) : Prop :=
    match a, b with
    | Reached ma, Reached mb => forall i j, entry ma i j = entry mb i j
    | Unreached, Unreached => True
    | _, _ => False
    end.
  Definition k_octagon : N := 1. (* STUB *)
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
  Lemma grow_incr_close : forall i j d m m', incr_close i j d m = Reached m' ->
    supp m' <= supp m + 4 /\
    b m' <= Nat.max (b m) (Nat.max (K.bits i) (K.bits j) + 1) /\
    ell m' <= Nat.max (ell m) (Z.size_nat d) + 4 /\
    M.weight m' <= M.weight m + 4 * (Nat.max (K.bits i) (K.bits j) + 2).
  Proof. Admitted. (* STUB *)

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
  Lemma coh_assign : forall x e s, coh s -> coh (assign x e s).
  Proof. Admitted. (* STUB *)
  Lemma coh_havoc : forall x s, coh s -> coh (havoc x s).
  Proof.
    intros x [|m] Hcoh; [exact I|]. intros i j.
    rewrite !entry_havoc. cbn [bar fst snd].
    destruct (X.eqb (fst i) x), (X.eqb (fst j) x); try reflexivity.
    apply Hcoh.
  Qed.
  Lemma coh_assume : forall g es s, coh s -> coh (assume g es s).
  Proof. Admitted. (* STUB *)
  Lemma coh_tclose : forall m, coherent m -> coh (tclose m).
  Proof. Admitted. (* PLAN-DEFECT: raw coherent entries may have repeated labels; keys then omits a signed twin pivot. OctagonTest.repeated_label_closure_asymmetric gives output bounds 2 and infinity from coherent input. A dbm_wf premise is needed for this label-based closure plan. *)
  Lemma coh_incr_close : forall i j d m, coherent m -> coh (incr_close i j d m).
  Proof. Admitted. (* STUB *)
  Lemma F_add_cons_twins : forall i j d m,
    entry (add_cons i j d m) i j = entry (add_cons i j d m) (bar j) (bar i).
  Proof. Admitted. (* PLAN-DEFECT: incoherent twins -100 and -2 stay unequal when d = 0. *)

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
  Lemma T1_fw : forall m, dbm_wf m ->
    (T_fw m <= k_octagon * N.of_nat
      ((supp m + 1)^3 * (b m + ell m + Nat.log2 (supp m) + 1)))%N.
  Proof. Admitted. (* STUB *)
  Lemma T0_fw_round : forall k m, dbm_wf m ->
    (T_fw_round k m <= k_octagon * N.of_nat
      ((supp m + 1)^2 * (b m + K.bits k + ell m + 1)))%N.
  Proof. Admitted. (* STUB *)
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
  Lemma T2_tighten : forall m, dbm_wf m ->
    (T_tighten m <= k_octagon * N.of_nat ((supp m + 1)^2 * (b m + ell m + 1)))%N.
  Proof. Admitted. (* STUB *)
  Lemma T3_strengthen : forall m, dbm_wf m ->
    (T_strengthen m <= k_octagon * N.of_nat ((supp m + 1)^2 * (b m + ell m + 1)))%N.
  Proof. Admitted. (* STUB *)
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
  Lemma tclose_tight : forall m m', dbm_wf m -> coherent m ->
    tclose m = Reached m' -> tightly_closed m'.
  Proof. Admitted. (* STUB *)
  Lemma incr_close_eq : forall m i j d, dbm_wf m -> tightly_closed m ->
    same_entries (incr_close i j d m) (tclose (add_cons i j d m)).
  Proof. Admitted. (* STUB *)
  Lemma bits_tclose_le : forall m m', tclose m = Reached m' ->
    ell m' <= ell m + Nat.log2 (supp m) + 1.
  Proof. Admitted. (* STUB *)
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
  Lemma bits_fw_trace_le : forall ks m k a, dbm_wf m ->
    In (k, a) (fw_trace ks m) ->
    ell a <= ell m + Nat.log2 (supp m) + 1.
  Proof. Admitted. (* STUB *)
  Lemma T0_fw : forall m, dbm_wf m ->
    (T_fw m <= k_octagon * (N.of_nat ((supp m + 1)^2 * (b m + ell m + 1)) +
      fold_right N.add 0%N (map (fun km => T_fw_round (fst km) (snd km))
        (fw_trace (keys m) m))))%N.
  Proof. Admitted. (* STUB *)
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
  Lemma T4_tclose : forall m, dbm_wf m ->
    (T_tclose m <= T_fw m + k_octagon * N.of_nat ((supp m + 1)^2 * (b m + ell m + 1)) +
      if diag_ok (fw m) then T_tighten (fw m) + T_strengthen (tighten (fw m)) else 0)%N.
  Proof. Admitted. (* STUB *)
  (** Tightening and strengthening keep the support. *)
  Lemma supp_tighten_strengthen : forall m,
    supp (tighten m) = supp m /\ b (tighten m) = b m /\
    supp (strengthen m) = supp m /\ b (strengthen m) = b m.
  Proof. Admitted. (* STUB *)
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
End OctagonT.
