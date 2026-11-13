(** * Certified polyhedral states

    Fourier-Motzkin elimination tracks combinations of the input constraints.
    For example, eliminating x from x + y <= 3 and -x <= -1 gives y <= 2.
    Builds on: PolySig, LinCertSig and the concrete binary trie. *)
From Stdlib Require Import List ZArith NArith QArith Bool Lia Ring.
From Argent Require Import Time Std.
From Galois.Base Require Import KeySig Trie.
From Galois.Lattice Require Import LatticeSig.
From Galois.Domains Require Import LangSig ValueSig.
From Galois.States Require Import EnvSig.
From Galois.Relational Require Import LinForm LinearizeSig NumStateSig LinCertSig PolySig.
Local Open Scope nat_scope.

Module Z.
  TimeFun Z.sgn.
End Z.

Module List.
  TimeFun List.find.
  TimeFun List.flat_map.
End List.

(** A strict flag belongs to an inequality and records a positive strict summand. *)
Record poly_row (X : Type) := PolyRow {
  poly_constraint : lcons X;
  poly_multipliers : list Z;
  poly_strict : bool
}.

Arguments poly_constraint {X} _.
Arguments poly_multipliers {X} _.
Arguments poly_strict {X} _.
TimeFun poly_constraint.
TimeFun poly_multipliers.
TimeFun poly_strict.

(** Repeated keys are summed before a row participates in elimination. *)
Definition poly_add_term {X} (encode : X -> positive)
    (acc : PTrieCode.t (X * Z)) (p : X * Z) : PTrieCode.t (X * Z) :=
  let key := encode (fst p) in
  let old := match PTrieCode.get key acc with Some q => snd q | None => 0%Z end in
  PTrieCode.set key (fst p, (old + snd p)%Z) acc.

TimeFun poly_add_term.

Definition poly_normal_coef {X} (encode : X -> positive) (xs : list (X * Z))
    : list (X * Z) :=
  PTrieCode.fold_values
    (fun acc p => if Z.eqb (snd p) 0 then acc else p :: acc)
    (fold_left (poly_add_term encode) xs PTrieCode.empty) nil.

TimeFun poly_normal_coef.

Definition poly_normal_row {X} (encode : X -> positive) (r : lcons X) : lcons X :=
  LCons X (poly_normal_coef encode (lhs r)) (lrel r) (rhs r).

TimeFun poly_normal_row.

Definition poly_coefficient {X} (eqb : X -> X -> bool) (x : X) (r : lcons X) : Z :=
  fold_right (fun p z => if eqb (fst p) x then (snd p + z)%Z else z) 0%Z (lhs r).

TimeFun poly_coefficient.

Definition poly_scale_coef {X} (a : Z) (xs : list (X * Z)) : list (X * Z) :=
  map (fun p => (fst p, (a * snd p)%Z)) xs.

TimeFun poly_scale_coef.

Fixpoint poly_weighted (a : Z) (ms : list Z) (b : Z) (ns : list Z) : list Z :=
  match ms, ns with
  | m :: ms, n :: ns => (a * m + b * n)%Z :: poly_weighted a ms b ns
  | _, _ => nil
  end.

TimeFun poly_weighted.

Definition poly_eq_used {X} (a : Z) (r : lcons X) : bool :=
  match lrel r with REq => true | RLe => Z.eqb a 0 end.

TimeFun poly_eq_used.

(** Only equality rows can carry a negative multiplier in an elimination step. *)
Definition poly_add_rows {X} (encode : X -> positive)
    (a : Z) (p : poly_row X) (b : Z) (q : poly_row X) : poly_row X :=
  let r := poly_constraint p in
  let s := poly_constraint q in
  PolyRow X
    (LCons X
      (poly_normal_coef encode (poly_scale_coef a (lhs r) ++ poly_scale_coef b (lhs s)))
      (if poly_eq_used a r && poly_eq_used b s then REq else RLe)
      (a * rhs r + b * rhs s)%Z)
    (poly_weighted a (poly_multipliers p) b (poly_multipliers q))
    (((0 <? a)%Z && poly_strict p) || ((0 <? b)%Z && poly_strict q)).

TimeFun poly_add_rows.

Definition poly_pad_row {X} (r : poly_row X) : poly_row X :=
  PolyRow X (poly_constraint r) (0%Z :: poly_multipliers r) (poly_strict r).

TimeFun poly_pad_row.

(** The initial multiplier vectors are the rows of the identity matrix. *)
Fixpoint poly_initial {X} (encode : X -> positive) (P : list (lcons X * bool))
    : list (poly_row X) :=
  match P with
  | nil => nil
  | p :: ps =>
    PolyRow X (poly_normal_row encode (fst p))
      (1%Z :: map (fun _ => 0%Z) ps) (snd p) ::
      map poly_pad_row (poly_initial encode ps)
  end.

TimeFun poly_initial.

Definition poly_pivot {X} (eqb : X -> X -> bool) (x : X) (r : poly_row X) : bool :=
  match lrel (poly_constraint r) with
  | REq => negb (Z.eqb (poly_coefficient eqb x (poly_constraint r)) 0)
  | RLe => false
  end.

TimeFun poly_pivot.

Definition poly_cancel {X} (encode : X -> positive) (eqb : X -> X -> bool)
    (x : X) (p r : poly_row X) : poly_row X :=
  let a := poly_coefficient eqb x (poly_constraint p) in
  let b := poly_coefficient eqb x (poly_constraint r) in
  if Z.eqb b 0 then r
  else poly_add_rows encode (- Z.sgn a * b)%Z p (Z.abs a) r.

TimeFun poly_cancel.

(** An equality pivot eliminates directly; otherwise every opposite-sign pair is combined. *)
Definition poly_step {X} (encode : X -> positive) (eqb : X -> X -> bool)
    (x : X) (P : list (poly_row X)) : list (poly_row X) :=
  match find (poly_pivot eqb x) P with
  | Some p => map (poly_cancel encode eqb x p) P
  | None =>
    let pos := filter (fun r => (0 <? poly_coefficient eqb x (poly_constraint r))%Z) P in
    let neg := filter (fun r => (poly_coefficient eqb x (poly_constraint r) <? 0)%Z) P in
    filter (fun r => Z.eqb (poly_coefficient eqb x (poly_constraint r)) 0) P ++
      flat_map (fun p => map (fun q =>
        poly_add_rows encode (- poly_coefficient eqb x (poly_constraint q))%Z p
          (poly_coefficient eqb x (poly_constraint p)) q) neg) pos
  end.

TimeFun poly_step.

Definition poly_variables {X} (encode : X -> positive) (P : list (lcons X)) : list X :=
  PTrieCode.fold_values (fun acc x => x :: acc)
    (fold_left (fun acc r =>
      fold_left (fun acc p => PTrieCode.set (encode (fst p)) (fst p) acc) (lhs r) acc)
      P PTrieCode.empty) nil.

TimeFun poly_variables.

Fixpoint poly_run {X} (encode : X -> positive) (eqb : X -> X -> bool)
    (xs : list X) (P : list (poly_row X)) : list (poly_row X) :=
  match xs with
  | nil => P
  | x :: xs => poly_run encode eqb xs (poly_step encode eqb x P)
  end.

TimeFun poly_run.

Definition poly_contradiction {X} (r : poly_row X) : bool :=
  let c := poly_constraint r in
  match lhs c with
  | nil =>
    match lrel c with
    | REq => negb (Z.eqb (rhs c) 0)
    | RLe => (rhs c <? 0)%Z || (poly_strict r && (rhs c <=? 0)%Z)
    end
  | _ :: _ => false
  end.

TimeFun poly_contradiction.

Definition poly_negate {X} (r : lcons X) : lcons X :=
  LCons X (poly_scale_coef (-1)%Z (lhs r)) RLe (- rhs r)%Z.

TimeFun poly_negate.

Definition poly_substitute {X} (encode : X -> positive) (eqb : X -> X -> bool)
    (x : X) (f : lin X) (r : lcons X) : lcons X :=
  let a := poly_coefficient eqb x r in
  LCons X
    (poly_normal_coef encode
      (filter (fun p => negb (eqb (fst p) x)) (lhs r) ++ poly_scale_coef a (coef f)))
    (lrel r) (rhs r - a * cst f)%Z.

TimeFun poly_substitute.

Definition poly_lower (z : Z) (b : bnd) : bnd :=
  match b with NegInf => Fin z | Fin n => Fin (Z.max z n) | PosInf => PosInf end.

TimeFun poly_lower.

Definition poly_upper (z : Z) (b : bnd) : bnd :=
  match b with PosInf => Fin z | Fin n => Fin (Z.min z n) | NegInf => NegInf end.

TimeFun poly_upper.

Module PolyCode (X : KEY_OPS) (L : LANG_OPS) (F : LINEARIZE_OPS X L)
    (C : LINCERT_OPS X) <: POLY_OPS X L F C.
  Definition t := reach (list (lcons X.t)).
  Definition wparam := unit.
  Definition subst (x : X.t) (f : lin X.t) (r : lcons X.t) : lcons X.t :=
    poly_substitute X.encode X.eqb x f r.

  Definition fm_elim (x : X.t) (P : list (lcons X.t)) : list (tracked X.t) :=
    map (fun r => Tracked X.t (poly_constraint r) (poly_multipliers r))
      (poly_step X.encode X.eqb x
        (poly_initial X.encode (map (fun r => (r, false)) P))).

  Definition candidate (P : list (lcons X.t)) (c : lcons X.t) (r : poly_row X.t)
      : option cert :=
    if poly_contradiction r then
      match poly_multipliers r with
      | sc :: ms =>
        let k := Cert ms (if C.check_empty P ms then 1%Z else sc) false in
        if C.check_entails P c k then Some k else None
      | nil => None
      end
    else None.

  Fixpoint find_certificate (P : list (lcons X.t)) (c : lcons X.t)
      (rs : list (poly_row X.t)) : option cert :=
    match rs with
    | nil => None
    | r :: rs =>
      match candidate P c r with
      | Some k => Some k
      | None => find_certificate P c rs
      end
    end.

  (** The complement is strict over Q; subtracting one would lose rational countermodels. *)
  Definition entail_cert (P : list (lcons X.t)) (c : lcons X.t) : option cert :=
    let input := (poly_negate c, true) :: map (fun r => (r, false)) P in
    find_certificate P c
      (poly_run X.encode X.eqb (poly_variables X.encode (c :: P))
        (poly_initial X.encode input)).

  Definition entails_row (P : list (lcons X.t)) (r : lcons X.t) : bool :=
    match entail_cert P r with Some k => C.check_entails P r k | None => false end.

  Definition keep_row (P : list (lcons X.t)) (r : lcons X.t) : bool :=
    match lrel r with
    | RLe => entails_row P r
    | REq => entails_row P (LCons X.t (lhs r) RLe (rhs r)) &&
        entails_row P (poly_negate r)
    end.

  Definition bot : t := Unreached.
  Definition is_bot (s : t) : bool :=
    match s with
    | Unreached => true
    | Reached P => entails_row P (LCons X.t nil RLe (-1)%Z)
    end.

  Definition leb (a b : t) : bool :=
    match a, b with
    | Unreached, _ => true
    | _, Unreached => is_bot a
    | Reached P, Reached Q => forallb (keep_row P) Q
    end.

  Definition join (a b : t) : t :=
    match a, b with
    | Unreached, _ => b
    | _, Unreached => a
    | Reached P, Reached Q => Reached (filter (keep_row Q) P ++ filter (keep_row P) Q)
    end.

  Definition top : t := Reached nil.
  Definition meet (a b : t) : t :=
    match a, b with
    | Reached P, Reached Q => Reached (P ++ Q)
    | _, _ => Unreached
    end.

  Definition widen (_ : wparam) (a b : t) : t :=
    match a, b with
    | Unreached, _ => if is_bot b then Unreached else b
    | _, Unreached => a
    | Reached P, Reached Q => Reached (filter (keep_row Q) P)
    end.

  Definition narrow (_ : t) (b : t) : t := b.

  Definition checked_projection (P : list (lcons X.t)) (x : X.t) (r : tracked X.t)
      : bool :=
    forallb (fun p => negb (X.eqb (fst p) x)) (lhs (row_of r)) &&
      C.check_entails P (row_of r) (Cert (mults_of r) 1 false).

  Definition havoc (x : X.t) (s : t) : t :=
    match s with
    | Unreached => Unreached
    | Reached P => Reached (map row_of (filter (checked_projection P x) (fm_elim x P)))
    end.

  Definition tmp_encode (x : option X.t) : positive :=
    match x with None => xH | Some y => xO (X.encode y) end.

  Definition tmp_eqb (x y : option X.t) : bool :=
    match x, y with
    | None, None => true
    | Some a, Some b => X.eqb a b
    | _, _ => false
    end.

  Definition rename_old (x y : X.t) : option X.t :=
    if X.eqb y x then None else Some y.

  Definition rename_row (f : X.t -> option X.t) (r : lcons X.t) : lcons (option X.t) :=
    LCons (option X.t) (map (fun p => (f (fst p), snd p)) (lhs r)) (lrel r) (rhs r).

  Fixpoint untag (xs : list (option X.t * Z)) : option (list (X.t * Z)) :=
    match xs with
    | nil => Some nil
    | (None, _) :: _ => None
    | (Some x, z) :: xs =>
      match untag xs with Some ys => Some ((x, z) :: ys) | None => None end
    end.

  Definition assignment_row (x : X.t) (f : lin X.t) : lcons (option X.t) :=
    LCons (option X.t)
      ((Some x, 1%Z) :: map (fun p => (rename_old x (fst p), (- snd p)%Z)) (coef f))
      REq (cst f).

  Definition assigned_candidate (P : list (lcons X.t)) (x : X.t) (f : lin X.t)
      (r : poly_row (option X.t)) : option (lcons X.t) :=
    match untag (lhs (poly_constraint r)), poly_multipliers r with
    | Some xs, _ :: ms =>
      let c := LCons X.t xs (lrel (poly_constraint r)) (rhs (poly_constraint r)) in
      if C.check_entails P (subst x f c) (Cert ms 1 false) then Some c else None
    | _, _ => None
    end.

  Definition assign_linear (x : X.t) (f : lin X.t) (P : list (lcons X.t))
      : list (lcons X.t) :=
    flat_map (fun r => match assigned_candidate P x f r with
      | Some c => c :: nil | None => nil end)
      (poly_step tmp_encode tmp_eqb None
        (poly_initial tmp_encode
          ((assignment_row x f, false) ::
           map (fun r => (rename_row (rename_old x) r, false)) P))).

  Definition assign (x : X.t) (e : term L.op X.t) (s : t) : t :=
    match s with
    | Unreached => Unreached
    | Reached P =>
      match F.lin_of e with
      | Some (f, NoWrap) => Reached (assign_linear x f P)
      | _ => havoc x s
      end
    end.

  Definition atom_row (a : atom X.t) : option (lcons X.t) :=
    match alw a, arw a with
    | NoWrap, NoWrap =>
      let cs := poly_normal_coef X.encode
        (coef (al a) ++ poly_scale_coef (-1)%Z (coef (ar a))) in
      let b := (cst (ar a) - cst (al a))%Z in
      Some (match acmp a with
        | CEq => LCons X.t cs REq b
        | CLe => LCons X.t cs RLe b
        | CLt => LCons X.t cs RLe (b - 1)%Z
        end)
    | _, _ => None
    end.

  Definition assume (g : L.guard) (es : list (term L.op X.t)) (s : t) : t :=
    match s with
    | Unreached => Unreached
    | Reached P => Reached
        (flat_map (fun a => match atom_row a with Some r => r :: nil | None => nil end)
          (F.atoms_of g es) ++ P)
    end.

  Definition range_row (f : lin X.t) : lcons (option X.t) :=
    LCons (option X.t)
      ((None, 1%Z) :: map (fun p => (Some (fst p), (- snd p)%Z)) (coef f))
      REq (cst f).

  Definition range_update (a b : Z) (is_eq : bool) (bounds : bnd * bnd) : bnd * bnd :=
    if (0 <? a)%Z then
      (if is_eq then poly_lower (- ((- b) / a))%Z (fst bounds) else fst bounds,
       poly_upper (b / a)%Z (snd bounds))
    else if (a <? 0)%Z then
      (poly_lower (- (b / (- a)))%Z (fst bounds),
       if is_eq then poly_upper ((- b) / (- a))%Z (snd bounds) else snd bounds)
    else bounds.

  Definition range_candidate (P : list (lcons X.t)) (f : lin X.t)
      (bounds : bnd * bnd) (r : poly_row (option X.t)) : bnd * bnd :=
    let c := poly_constraint r in
    if forallb (fun p => match fst p with None => true | Some _ => false end) (lhs c) then
      let a := poly_coefficient tmp_eqb None c in
      let conclusion := LCons X.t (poly_scale_coef a (coef f)) (lrel c)
        (rhs c - a * cst f)%Z in
      match poly_multipliers r with
      | _ :: ms =>
        if C.check_entails P conclusion (Cert ms 1 false) then
          range_update a (rhs c)
            (match lrel c with REq => true | RLe => false end) bounds
        else bounds
      | nil => bounds
      end
    else bounds.

  Definition range_linear (P : list (lcons X.t)) (f : lin X.t) : bnd * bnd :=
    let input := range_row f :: map (rename_row (@Some X.t)) P in
    let vars := poly_variables X.encode (LCons X.t (coef f) REq (cst f) :: P) in
    fold_left (range_candidate P f)
      (poly_run tmp_encode tmp_eqb (map (@Some X.t) vars)
        (poly_initial tmp_encode (map (fun r => (r, false)) input))) (NegInf, PosInf).

  Definition range (e : term L.op X.t) (s : t) : bnd * bnd :=
    match s with
    | Unreached => (NegInf, PosInf)
    | Reached P =>
      match F.lin_of e with
      | Some (f, NoWrap) => range_linear P f
      | Some (_, WrapTo lo hi) => if (lo <=? hi)%Z then (Fin lo, Fin hi) else (NegInf, PosInf)
      | None => (NegInf, PosInf)
      end
    end.
End PolyCode.

Module Poly (X : KEY) (L : LANG) (N : NUM_VIEW L)
    (F : LINEARIZE X L N) (C : LINCERT X) <: POLY X L N F C.
  Include PolyCode X L F C.
  Definition wrank (_ : wparam) (s : t) : nat :=
    match s with Unreached => 0 | Reached P => length P end.
  Definition ngamma (s : t) (v : X.t -> Z) : Prop :=
    match s with Unreached => False | Reached P => Forall (sat v) P end.

  (** Scaling every stored occurrence scales its integer evaluation. *)
  Lemma eval_coef_scale : forall (v : X.t -> Z) a xs,
    eval_coef v (poly_scale_coef a xs) = (a * eval_coef v xs)%Z.
  Proof.
    intros v a xs. unfold eval_coef, poly_scale_coef.
    induction xs as [|[x b] xs IH]; cbn [map fold_right fst snd].
    - ring.
    - rewrite IH. ring.
  Qed.

  (** A returned candidate passes the checker and never requests an integer cut. *)
  Lemma candidate_returned : forall P c r k, candidate P c r = Some k ->
    C.check_entails P c k = true /\ cut k = false.
  Proof.
    intros P c r k Hresult. unfold candidate in Hresult.
    destruct (poly_contradiction r); [| discriminate].
    destruct (poly_multipliers r) as [|sc ms]; [discriminate |].
    destruct (C.check_entails P c
      (Cert ms (if C.check_empty P ms then 1%Z else sc) false)) eqn:Hcheck;
      [| discriminate].
    injection Hresult as Hsame. subst k. split; [exact Hcheck | reflexivity].
  Qed.

  (** Searching candidates preserves their checker result and cut flag. *)
  Lemma find_certificate_returned : forall P c rs k, find_certificate P c rs = Some k ->
    C.check_entails P c k = true /\ cut k = false.
  Proof.
    intros P c rs. induction rs as [|r rs IH]; intros k Hresult;
      cbn [find_certificate] in Hresult; [discriminate |].
    destruct (candidate P c r) as [j|] eqn:Hcandidate.
    - injection Hresult as Hsame. subst j. now apply candidate_returned with (r := r).
    - now apply IH.
  Qed.

  (** Every produced entailment certificate is checked and is valid without cuts. *)
  Lemma entail_cert_returned : forall P c k, entail_cert P c = Some k ->
    C.check_entails P c k = true /\ cut k = false.
  Proof.
    intros P c k Hresult. unfold entail_cert in Hresult.
    now apply find_certificate_returned in Hresult.
  Qed.

  (** Successful row inclusion retains every integer model of its input. *)
  Lemma entails_row_sound : forall P r v,
    entails_row P r = true -> Forall (sat v) P -> sat v r.
  Proof.
    intros P r v Hcheck Hmodels. unfold entails_row in Hcheck.
    destruct (entail_cert P r) as [k|]; [| discriminate].
    exact (C.check_entails_sound P r k Hcheck v Hmodels).
  Qed.

  (** Splitting an equality into two inequalities preserves its meaning. *)
  Lemma keep_row_sound : forall P r v,
    keep_row P r = true -> Forall (sat v) P -> sat v r.
  Proof.
    intros P r v Hkeep Hmodels. unfold keep_row in Hkeep.
    destruct (lrel r) eqn:Hrel.
    - apply andb_true_iff in Hkeep as [Hupper Hlower].
      pose proof (entails_row_sound P _ v Hupper Hmodels) as Hle.
      pose proof (entails_row_sound P _ v Hlower Hmodels) as Hge.
      unfold sat, poly_negate in Hle, Hge. cbn [lhs lrel rhs] in Hle, Hge.
      rewrite eval_coef_scale in Hge. unfold sat. rewrite Hrel. lia.
    - exact (entails_row_sound P r v Hkeep Hmodels).
  Qed.

  (** A state recognized as bottom has no integer model. *)
  Lemma is_bot_sound : forall s v, is_bot s = true -> ~ ngamma s v.
  Proof.
    intros [|P] v Hbot Hmodels; [exact Hmodels |].
    pose proof (entails_row_sound P _ v Hbot Hmodels) as Hfalse.
    cbn [sat lrel lhs rhs eval_coef fold_right] in Hfalse. lia.
  Qed.

  (** A coefficient list that omits the updated key keeps its evaluation. *)
  Lemma eval_coef_havoc : forall x st c xs,
    forallb (fun p => negb (X.eqb (fst p) x)) xs = true ->
    eval_coef (fun y => N.num (upd X.eqb st x c y)) xs =
      eval_coef (fun y => N.num (st y)) xs.
  Proof.
    intros x st c xs. unfold eval_coef.
    induction xs as [|[y a] xs IH]; intro Hfree; [reflexivity |].
    cbn [forallb fst] in Hfree. apply andb_true_iff in Hfree as [Hhead Htail].
    apply negb_true_iff in Hhead.
    change (a * N.num (if X.eqb y x then c else st y) +
      eval_coef (fun z => N.num (upd X.eqb st x c z)) xs =
      a * N.num (st y) + eval_coef (fun z => N.num (st z)) xs)%Z.
    rewrite Hhead. f_equal. exact (IH Htail).
  Qed.

  (** Checked projection rows hold after any replacement of the omitted variable. *)
  Lemma checked_projection_sound : forall P x r st c,
    checked_projection P x r = true -> Forall (sat (fun y => N.num (st y))) P ->
    sat (fun y => N.num (upd X.eqb st x c y)) (row_of r).
  Proof.
    intros P x r st c Hchecked Hmodels. unfold checked_projection in Hchecked.
    apply andb_true_iff in Hchecked as [Hfree Hcheck].
    pose proof (C.check_entails_sound P (row_of r) (Cert (mults_of r) 1 false)
      Hcheck (fun y => N.num (st y)) Hmodels) as Hsat.
    unfold sat in *. rewrite (eval_coef_havoc x st c (lhs (row_of r)) Hfree).
    exact Hsat.
  Qed.
  Lemma leb_refl  : forall a, leb a a = true.
  Proof. Admitted. (* STUB *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof. Admitted. (* STUB *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof.
    destruct a; reflexivity.
  Qed.
  Lemma is_bot_bot : is_bot bot = true.
  Proof.
    reflexivity.
  Qed.
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof. Admitted. (* STUB *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof. Admitted. (* STUB *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof. Admitted. (* STUB *)
  Lemma top_greatest : forall a, leb a top = true.
  Proof.
    destruct a; reflexivity.
  Qed.
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
  Proof.
    intros [|P] [|Q] v Hle Hmodels; cbn [ngamma] in *; try contradiction.
    - exact (is_bot_sound (Reached P) v Hle Hmodels).
    - apply Forall_forall. intros r Hin. apply keep_row_sound with (P := P).
      + exact (proj1 (forallb_forall _ _) Hle r Hin).
      + exact Hmodels.
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
  Proof. Admitted. (* STUB *)
  Lemma havoc_sound : forall x s st c, ngamma s (fun y => N.num (st y)) ->
    ngamma (havoc x s) (fun y => N.num (upd X.eqb st x c y)).
  Proof.
    intros x [|P] st c Hmodels; [contradiction |].
    change (Forall (sat (fun y => N.num (upd X.eqb st x c y)))
      (map row_of (filter (checked_projection P x) (fm_elim x P)))).
    apply Forall_forall. intros r Hin.
    apply in_map_iff in Hin as [q [Hsame Hin]]. subst r.
    apply filter_In in Hin as [_ Hchecked].
    exact (checked_projection_sound P x q st c Hchecked Hmodels).
  Qed.
  Lemma assume_sound : forall g es s st cs,
    ngamma s (fun y => N.num (st y)) -> eval_terms L.eval st es = Some cs ->
    L.holds g cs -> ngamma (assume g es s) (fun y => N.num (st y)).
  Proof. Admitted. (* STUB *)
  Lemma range_sound : forall e s st c,
    ngamma s (fun y => N.num (st y)) -> eval_term L.eval st e = Some c ->
    in_bnd (fst (range e s)) (snd (range e s)) (N.num c).
  Proof. Admitted. (* STUB *)
  Lemma ngamma_reached : forall P v, ngamma (Reached P) v <-> Forall (sat v) P.
  Proof.
    intros P v. reflexivity.
  Qed.
  Lemma ngamma_unreached : forall v, ~ ngamma Unreached v.
  Proof.
    intros v Hfalse. exact Hfalse.
  Qed.
End Poly.

Module PolyT (X : KEY_T) (L : LANG_T) (N : NUM_VIEW L)
    (F : LINEARIZE_T X L N) (C : LINCERT_T X) <: POLY_ALL X L N F C.
  Include Poly X L N F C.
  Definition wsize (_ : wparam) : nat := 0.
  Definition normal (P : list (lcons X.t)) : Prop :=
    Forall (fun r => NoDup (map fst (lhs r))) P.
  Definition normal_s (s : t) : Prop :=
    match s with Unreached => True | Reached P => normal P end.
  Definition vars_of (P : list (lcons X.t)) : list X.t :=
    fold_left (fun acc x => if existsb (X.eqb x) acc then acc else x :: acc)
      (flat_map (fun r => map fst (lhs r)) P) nil.
  Definition n (P : list (lcons X.t)) : nat := length P + length (vars_of P).
  Definition ell (P : list (lcons X.t)) : nat :=
    fold_right Nat.max 0 (map C.row_bits P) +
    fold_right Nat.max 0 (map C.row_key_bits P).
  Definition prows (s : t) : list (lcons X.t) :=
    match s with Unreached => nil | Reached P => P end.
  Definition wunits (_ : t) : nat := 0.
  Definition terms (s : t) : nat :=
    fold_right Nat.add 0 (map (fun r => length (lhs r)) (prows s)).
  Definition nell (s : t) : nat := ell (prows s) + Nat.log2 (terms s) + 1.
  Definition mu (s : t) : nat := terms s + n (prows s) + nell s.
  Definition lat (m : nat) : nat :=
    2 * (m + 1) * (fmcost m (m + 1) m (m + 1) (m + 1) + m^2 + 1).
  Definition size (s : t) : nat := lat (2 * mu s).
  Definition k_poly : N := 1. (* STUB *)
  Definition assign_work (x : X.t) (e : term L.op X.t) (s : t) : nat :=
    terms s * (nell s + 1) +
      (length (prows s) + 3)^2 *
      (n (prows s) + terms s + tsize e + length (prows s) + 3) *
      (nell s + X.bits x + F.bits_e e + 1)^2 + N.to_nat (F.T_lin_of e).
  Definition havoc_work (x : X.t) (s : t) : nat :=
    terms s * (nell s + 1) +
      (length (prows s) + 1)^2 * (n (prows s) + terms s + length (prows s) + 1) *
      (nell s + X.bits x + 1)^2.
  Definition assume_work (g : L.guard) (es : list (term L.op X.t)) (s : t) : nat :=
    (length (prows s) + 1) * (length (F.atoms_of g es) + 1) *
      (fold_right Nat.add 0%nat (map tsize es) + 1) *
      (F.bits_es g es + Nat.log2 (fold_right Nat.add 0%nat (map tsize es)) + 1) +
      N.to_nat (F.T_atoms_of g es).
  Definition range_work (e : term L.op X.t) (s : t) : nat :=
    terms s * (nell s + 1) +
      fmcost (n (prows s) + tsize e) (length (prows s) + 2) (n (prows s) + tsize e)
        (length (prows s) + 2) (nell s + F.bits_e e + 1) + N.to_nat (F.T_lin_of e).
  Definition range_bits (e : term L.op X.t) (s : t) : nat := range_work e s.
  TimeFun subst.
  TimeFun fm_elim.
  TimeFun candidate.
  TimeFun find_certificate.
  TimeFun entail_cert.
  TimeFun entails_row.
  TimeFun keep_row.
  TimeFun bot.
  TimeFun is_bot.
  TimeFun leb.
  TimeFun join.
  TimeFun top.
  TimeFun meet.
  TimeFun widen.
  TimeFun narrow.
  TimeFun checked_projection.
  TimeFun havoc.
  TimeFun tmp_encode.
  TimeFun tmp_eqb.
  TimeFun rename_old.
  TimeFun rename_row.
  TimeFun untag.
  TimeFun assignment_row.
  TimeFun assigned_candidate.
  TimeFun assign_linear.
  TimeFun assign.
  TimeFun atom_row.
  TimeFun assume.
  TimeFun range_row.
  TimeFun range_update.
  TimeFun range_candidate.
  TimeFun range_linear.
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
  Definition c_poly : N := 1. (* STUB *)
  Lemma T_subst_le : forall x f r,
    (T_subst x f r <= c_poly * N.of_nat
      ((X.bits x + C.lsize (LCons _ (coef f) REq (cst f)) + C.lsize r + 1)^2))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_fm_elim_le : forall x P, normal P ->
    (T_fm_elim x P <= c_poly * N.of_nat (((length P + 1)^2)%nat) *
      N.of_nat ((n P + length P + 1)%nat) * N.of_nat (((ell P + 1)^2)%nat))%N.
  Proof. Admitted. (* STUB *)
  Lemma T_entail_cert_le : forall P c, normal P -> normal (c :: nil) ->
    (T_entail_cert P c <= c_poly *
      N.of_nat (fmcost (n P + length (lhs c)) (length P + 1)
        (n P + length (lhs c)) (length P + 1)
        (ell P + C.row_bits c + C.row_key_bits c)))%N.
  Proof. Admitted. (* STUB *)
  (** Assignment charges row normalization and one elimination after linearization. *)
  Lemma F_assign_work : forall x e s,
    (N.of_nat (assign_work x e s) = N.of_nat (terms s * (nell s + 1) +
      (length (prows s) + 3)^2 *
      (n (prows s) + terms s + tsize e + length (prows s) + 3) *
      (nell s + X.bits x + F.bits_e e + 1)^2) + F.T_lin_of e)%N.
  Proof.
    intros x e s. unfold assign_work. rewrite Nat2N.inj_add, N2Nat.id. reflexivity.
  Qed.
  (** Havoc charges row normalization and one elimination of the selected variable. *)
  Lemma F_havoc_work : forall x s,
    havoc_work x s = terms s * (nell s + 1) +
      (length (prows s) + 1)^2 * (n (prows s) + terms s + length (prows s) + 1) *
      (nell s + X.bits x + 1)^2.
  Proof.
    reflexivity.
  Qed.
  (** Assumption charges every emitted atom and the bits of its merged coefficients. *)
  Lemma F_assume_work : forall g es s,
    (N.of_nat (assume_work g es s) =
      N.of_nat ((length (prows s) + 1) * (length (F.atoms_of g es) + 1) *
        (fold_right Nat.add 0%nat (map tsize es) + 1) *
        (F.bits_es g es + Nat.log2 (fold_right Nat.add 0%nat (map tsize es)) + 1)) +
      F.T_atoms_of g es)%N.
  Proof.
    intros g es s. unfold assume_work. rewrite Nat2N.inj_add, N2Nat.id. reflexivity.
  Qed.
  Definition k_cert : N := 1%N. (* STUB *)
  Lemma T_entail_cert_raw : forall P c,
    (T_entail_cert P c <= k_cert * N.of_nat
      (terms (Reached (c :: P)) * (nell (Reached (c :: P)) + 1) +
       fmcost (n P + length (lhs c)) (length P + 1) (n P + length (lhs c))
         (length P + 1) (nell (Reached (c :: P)))))%N.
  Proof. Admitted. (* STUB *)
  Lemma entail_cert_size : forall P c k, entail_cert P c = Some k ->
    (N.of_nat (C.csize P (mults k) + (Z.size_nat (scale k) + 1) *
        (C.lsize c + C.cbits P (mults k) + 1)) <=
      k_cert * N.of_nat
        (terms (Reached (c :: P)) * (nell (Reached (c :: P)) + 1) +
         fmcost (n P + length (lhs c)) (length P + 1) (n P + length (lhs c))
           (length P + 1) (nell (Reached (c :: P)))))%N.
  Proof. Admitted. (* STUB *)
  Lemma fm_mults_size : forall x P r, normal P -> In r (fm_elim x P) ->
    length (mults_of r) = length P /\
    Forall (fun m => Z.size_nat m <= ell P + 1) (mults_of r).
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
  Lemma fm_step_mults : forall P x r, In r (fm_elim x P) ->
    exists s, C.combine P (mults_of r) = Some s /\ lrel s = lrel (row_of r) /\
      rhs s = rhs (row_of r) /\
      forall v : X.t -> Z, eval_coef v (lhs s) = eval_coef v (lhs (row_of r)).
  Proof. Admitted. (* STUB *)
  Lemma entail_cert_checks : forall P c k,
    entail_cert P c = Some k -> C.check_entails P c k = true.
  Proof.
    intros P c k Hresult. exact (proj1 (entail_cert_returned P c k Hresult)).
  Qed.
  (** Generated entailment certificates use rationally valid combinations. *)
  Lemma entail_cert_nocut : forall P c k, entail_cert P c = Some k -> cut k = false.
  Proof.
    intros P c k Hresult. exact (proj2 (entail_cert_returned P c k Hresult)).
  Qed.
  (** Elimination keeps rows free of repeated keys. *)
  Lemma normal_fm_elim : forall x P, normal P -> normal (map row_of (fm_elim x P)).
  Proof. Admitted. (* STUB *)
  Lemma fm_complete_Q : forall P c, lrel c = RLe -> entail_cert P c = None ->
    exists v : X.t -> Q, Forall (satQ v) P /\ ~ satQ v c.
  Proof. Admitted. (* STUB *)
  Lemma fm_rows_le : forall x P, length (fm_elim x P) <= (length P)^2 / 4 + length P.
  Proof. Admitted. (* STUB *)
  Lemma ell_fm_le : forall x P, normal P ->
    ell (map row_of (fm_elim x P)) <= 2 * ell P + 1.
  Proof. Admitted. (* STUB *)
  Lemma subst_sat : forall v x f r, sat v (subst x f r) <->
    sat (upd X.eqb v x (eval_lin v f)) r.
  Proof. Admitted. (* STUB *)
  Lemma wrank_rows : forall p P, wrank p (Reached P) = length P.
  Proof. Admitted. (* STUB *)
  Definition keep (P : list (lcons X.t)) (r : lcons X.t) : bool := keep_row P r.
  TimeFun keep.
  Definition entails (P : list (lcons X.t)) (r : lcons X.t) : bool :=
    match entail_cert P r with Some k => C.check_entails P r k | None => false end.
  Lemma F_leb_keep : forall a b, leb (Reached b) (Reached a) = forallb (keep b) a.
  Proof. Admitted. (* STUB *)
  Lemma F_widen_keep : forall p a b,
    widen p (Reached a) (Reached b) = Reached (filter (keep b) a).
  Proof. Admitted. (* STUB *)
  Lemma F_leb_split : forall a b, leb (Reached a) (Reached b) =
    forallb (fun r => match lrel r with
      | RLe => entails a r
      | REq => andb (entails a (LCons _ (lhs r) RLe (rhs r)))
          (entails a (LCons _ (map (fun p => (fst p, (- snd p)%Z)) (lhs r)) RLe
            (- rhs r)%Z))
      end) b.
  Proof. Admitted. (* STUB *)
  (** State size charges all stored numeric data. *)
  Lemma lat_size : forall a b, lat (mu a + mu b) <= size a + size b.
  Proof. Admitted. (* STUB *)
  Lemma T1_leb : forall a b,
    (T_leb a b <= k_poly * N.of_nat (lat (mu a + mu b)))%N.
  Proof. Admitted. (* STUB *)
  Lemma T1_join : forall a b,
    (T_join a b <= k_poly * N.of_nat (lat (mu a + mu b)))%N.
  Proof. Admitted. (* STUB *)
  Lemma T1_widen : forall p a b,
    (T_widen p a b <= k_poly * N.of_nat (lat (mu a + mu b)))%N.
  Proof. Admitted. (* STUB *)
  Lemma T1_narrow : forall a b,
    (T_narrow a b <= k_poly * N.of_nat (lat (mu a + mu b)))%N.
  Proof. Admitted. (* STUB *)
  Lemma F_size : forall s, size s = lat (2 * mu s).
  Proof. Admitted. (* STUB *)
  (** Range work charges the numeric query and its linearization. *)
  Lemma F_range_work : forall e s, (N.of_nat (range_work e s) =
    N.of_nat (terms s * (nell s + 1) +
      fmcost (n (prows s) + tsize e) (length (prows s) + 2) (n (prows s) + tsize e)
        (length (prows s) + 2) (nell s + F.bits_e e + 1)) + F.T_lin_of e)%N.
  Proof. Admitted. (* STUB *)
  Lemma F_range_bits : forall e s, range_bits e s = range_work e s.
  Proof. Admitted. (* STUB *)
End PolyT.
