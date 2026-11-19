(** * Lawful merges of lattice tables, built

    This file builds the merges of [LatticeMergeSig.v]. [lift_merge] lifts a join of decoded
    values to engine values. It joins the values that two positives encode, puts a positive that
    encodes no value below every encoding, and merges two such positives by [Pos.max]. A
    positive that the decoder maps to a value with another encoding encodes no value, so a lifted
    join has the laws of the engine for every encoder. [MaxMerge] merges by [Pos.max] at every
    code, [DecodedMerge] adds a join at its code to a merge, and [MergeValue] is the value module
    of positives with a primitive set and a merge. The lemma [lat_merge_moves] of [MergeValue]
    moves the meaning of a specification from the merge of the primitives to such a merge.

    For example, [lift_merge NEncode.encode NEncode.decode N.lor] merges the encodings of the
    sets [1] and [2] into the encoding of [3], and it merges the positive [3], which encodes no
    value of [N], with the encoding of [1] into the encoding of [1].

    Main results
    - [lift_merge_comm], [lift_merge_assoc], [lift_merge_idem] A lifted join has the laws of the
      engine at every positive.
    - [lift_merge_encode] On encodings, a lifted join encodes the join.
    - [lat_merge_agrees_at] The meaning of a specification depends on the merge only at the
      codes of its lattice tables, and at each table only at the values of a predicate that
      holds of the values assigned there and that the merge keeps.
    - [MaxMerge], [DecodedMerge] Merges at every code, with joins at some codes.
    - [MergeValue] A value module with such a merge. Its lemma [lat_merge_moves] moves the
      meaning of a specification from the merge of the primitives to the merge of the module.

    Builds on: the signatures of lawful merges, the meaning of lattice reads, the encoders of
    values, the value modules of the engine and the keys of positives. *)

From Stdlib Require Import List PArith Bool.
From Argent Require Import Time Std.
From Galois.Base Require Import KeySig Key.
From Galois.Egglog Require Import ValueSig Syntax Model.
From Galois.Front Require Import EncodeSig Spec SpecLattice DeriveLattice LatticeMergeSig.

Import List.ListNotations.

(** * Positives *)

(** The encoder of positives, which are their own engine values. *)
Module PosEncode <: ENCODE.
  Definition t : Type := positive.
  Definition encode (p : positive) : positive := p.
  Definition decode (p : positive) : option positive := Some p.
  TimeFun encode.
  TimeFun decode.

  Lemma decode_encode : forall x, decode (encode x) = Some x.
  Proof.
    reflexivity.
  Qed.
End PosEncode.

(** * Lifted joins *)

(** The larger of two positives. *)
Definition pos_max (a b : positive) : positive := if Pos.leb a b then b else a.

TimeFun pos_max.

(** [pos_max] is [Pos.max]. *)
Lemma pos_max_spec : forall a b, pos_max a b = Pos.max a b.
Proof.
  intros a b.
  unfold pos_max.
  destruct (Pos.leb_spec a b) as [Hab | Hba].
  - symmetry. apply Pos.max_r. exact Hab.
  - symmetry. apply Pos.max_l. apply Pos.lt_le_incl. exact Hba.
Qed.

(** The value that an engine value encodes. A positive that [decode] maps to a value with
    another encoding encodes no value. *)
Definition canon_decode {T : Type} (encode : T -> positive) (decode : positive -> option T)
    (a : positive) : option T :=
  match decode a with
  | Some x => if Pos.eqb (encode x) a then Some x else None
  | None => None
  end.

TimeFun canon_decode.

(** The engine value of the join of the values that two engine values encode. A positive that
    encodes no value is below every encoding, and two such positives merge by [Pos.max]. *)
Definition lift_merge {T : Type} (encode : T -> positive) (decode : positive -> option T)
    (join : T -> T -> T) (a b : positive) : positive :=
  match canon_decode encode decode a, canon_decode encode decode b with
  | Some x, Some y => encode (join x y)
  | Some _, None => a
  | None, Some _ => b
  | None, None => pos_max a b
  end.

TimeFun lift_merge.

Section Lift.
Context {T : Type} (encode : T -> positive) (decode : positive -> option T)
  (join : T -> T -> T).
Hypothesis decode_encode : forall x, decode (encode x) = Some x.

(** An encoding encodes its value. *)
Lemma canon_decode_encode : forall x, canon_decode encode decode (encode x) = Some x.
Proof.
  intros x.
  unfold canon_decode.
  rewrite decode_encode, Pos.eqb_refl.
  reflexivity.
Qed.

(** A positive that encodes a value is the encoding of the value. *)
Lemma canon_decode_some : forall a x, canon_decode encode decode a = Some x -> encode x = a.
Proof.
  intros a x.
  unfold canon_decode.
  destruct (decode a) as [y |]; [| discriminate].
  destruct (Pos.eqb_spec (encode y) a) as [Hy | _]; [| discriminate].
  intros Hxy.
  injection Hxy as Hxy.
  subst y.
  exact Hy.
Qed.

(** The larger of two positives that encode no value encodes no value. *)
Lemma canon_decode_max : forall a b, canon_decode encode decode a = None ->
  canon_decode encode decode b = None -> canon_decode encode decode (Pos.max a b) = None.
Proof.
  intros a b Ha Hb.
  destruct (Pos.max_spec a b) as [[_ Hmax] | [_ Hmax]]; rewrite Hmax; assumption.
Qed.

(** A lifted join, from the values that its two positives encode. *)
Definition lift_with (oa ob : option T) (a b : positive) : positive :=
  match oa, ob with
  | Some x, Some y => encode (join x y)
  | Some _, None => a
  | None, Some _ => b
  | None, None => Pos.max a b
  end.

(** A lifted join reads the values that its positives encode. *)
Lemma lift_merge_unfold : forall a b,
  lift_merge encode decode join a b =
    lift_with (canon_decode encode decode a) (canon_decode encode decode b) a b.
Proof.
  intros a b.
  unfold lift_merge, lift_with.
  destruct (canon_decode encode decode a), (canon_decode encode decode b);
    [reflexivity | reflexivity | reflexivity | apply pos_max_spec].
Qed.

(** A lifted join encodes the join of the values that its positives encode, the one value that
    one of them encodes, or no value. *)
Lemma canon_lift_merge : forall a b,
  canon_decode encode decode (lift_merge encode decode join a b) =
    match canon_decode encode decode a, canon_decode encode decode b with
    | Some x, Some y => Some (join x y)
    | Some x, None => Some x
    | None, Some y => Some y
    | None, None => None
    end.
Proof.
  intros a b.
  rewrite lift_merge_unfold.
  destruct (canon_decode encode decode a) as [x |] eqn:Ha,
    (canon_decode encode decode b) as [y |] eqn:Hb; cbn [lift_with].
  - apply canon_decode_encode.
  - exact Ha.
  - exact Hb.
  - exact (canon_decode_max a b Ha Hb).
Qed.

(** On encodings, a lifted join encodes the join. *)
Lemma lift_merge_encode : forall x y,
  lift_merge encode decode join (encode x) (encode y) = encode (join x y).
Proof.
  intros x y.
  unfold lift_merge.
  rewrite !canon_decode_encode.
  reflexivity.
Qed.

Hypothesis join_comm : forall x y, join x y = join y x.
Hypothesis join_assoc : forall x y z, join x (join y z) = join (join x y) z.
Hypothesis join_idem : forall x, join x x = x.

(** Merge order does not affect a lifted join. *)
Lemma lift_merge_comm : forall a b,
  lift_merge encode decode join a b = lift_merge encode decode join b a.
Proof.
  intros a b.
  rewrite !lift_merge_unfold.
  destruct (canon_decode encode decode a) as [x |], (canon_decode encode decode b) as [y |];
    cbn [lift_with].
  - rewrite join_comm. reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Pos.max_comm.
Qed.

(** Grouping does not affect a lifted join. *)
Lemma lift_merge_assoc : forall a b c,
  lift_merge encode decode join a (lift_merge encode decode join b c) =
    lift_merge encode decode join (lift_merge encode decode join a b) c.
Proof.
  intros a b c.
  rewrite (lift_merge_unfold a (lift_merge encode decode join b c)),
    (lift_merge_unfold (lift_merge encode decode join a b) c),
    (canon_lift_merge b c), (canon_lift_merge a b), (lift_merge_unfold b c),
    (lift_merge_unfold a b).
  destruct (canon_decode encode decode a) as [x |], (canon_decode encode decode b) as [y |],
    (canon_decode encode decode c) as [z |]; cbn [lift_with].
  - rewrite join_assoc. reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - reflexivity.
  - apply Pos.max_assoc.
Qed.

(** Merging a positive with itself leaves it unchanged. *)
Lemma lift_merge_idem : forall a, lift_merge encode decode join a a = a.
Proof.
  intros a.
  rewrite lift_merge_unfold.
  destruct (canon_decode encode decode a) as [x |] eqn:Ha; cbn [lift_with].
  - rewrite join_idem. exact (canon_decode_some a x Ha).
  - apply Pos.max_id.
Qed.

End Lift.

(** * Codes of lattice tables *)

(** The merge codes of the lattice tables of a list of declarations. *)
Definition lat_codes (ds : list decl) : list positive :=
  flat_map (fun d => match out d with OLat m => [m] | _ => [] end) ds.

(** The merge code of a lattice table is a merge code of the declarations. *)
Lemma lookup_kind_lat_codes : forall ds f m,
  lookup_kind ds f = Some (OLat m) -> In m (lat_codes ds).
Proof.
  induction ds as [| d ds IH]; intros f m Hkind; cbn in Hkind |- *; [discriminate |].
  apply in_or_app.
  destruct (Pos.eqb (name d) f).
  - left. injection Hkind as Hout. rewrite Hout. left. reflexivity.
  - right. exact (IH f m Hkind).
Qed.

(** Every merge code of a lattice table is in [cs] when a computation says that every merge code
    of the declarations is. *)
Lemma lat_codes_covered : forall ds cs f m,
  forallb (fun m => existsb (Pos.eqb m) cs) (lat_codes ds) = true ->
  lookup_kind ds f = Some (OLat m) -> In m cs.
Proof.
  intros ds cs f m Hall Hkind.
  rewrite forallb_forall in Hall.
  pose proof (Hall m (lookup_kind_lat_codes ds f m Hkind)) as Hin.
  apply existsb_exists in Hin.
  destruct Hin as [m' [Hm' Heq]].
  apply Pos.eqb_eq in Heq.
  subst m'.
  exact Hm'.
Qed.

(** * Moving the meaning between merges *)

Section Moves.
Context {V : Type} (prim : positive -> list V -> option V)
  (merge1 merge2 : positive -> V -> V -> V) (ok : positive -> V -> Prop) (s : spec V)
  (I : positive -> list V -> Prop).
Hypothesis agree : forall f m a b, lookup_kind (tables s) f = Some (OLat m) -> ok f a ->
  ok f b -> merge1 m a b = merge2 m a b.
Hypothesis keeps : forall f m a b, lookup_kind (tables s) f = Some (OLat m) -> ok f a ->
  ok f b -> ok f (merge1 m a b).
Hypothesis assigned_ok : forall f ks w, lat_assigned prim merge1 s I f ks w -> ok f w.

(** The meaning with [merge1] is contained in the meaning with [merge2], and a value that a read
    sees with [merge1] is a value of [ok]. *)
Lemma lat_merge_forward :
  (forall r vs, lat_derived prim merge1 s I r vs -> lat_derived prim merge2 s I r vs) /\
  (forall f ks w, lat_assigned prim merge1 s I f ks w -> lat_assigned prim merge2 s I f ks w) /\
  (forall f ks w, lat_merged prim merge1 s I f ks w -> lat_merged prim merge2 s I f ks w).
Proof.
  destruct (lat_least prim merge1 s I
    (fun r vs => lat_derived prim merge1 s I r vs /\ lat_derived prim merge2 s I r vs)
    (fun f ks w => lat_assigned prim merge1 s I f ks w /\ lat_assigned prim merge2 s I f ks w)
    (fun f ks w => lat_merged prim merge1 s I f ks w /\ ok f w /\
      lat_merged prim merge2 s I f ks w))
    as [Hrows [Hvalues Hmerged]].
  - intros r vs Hin HI. split; apply lat_derived_input; assumption.
  - intros f ks w [H1 H2].
    split; [exact (lat_merged_one prim merge1 s I f ks w H1) |].
    split; [exact (assigned_ok f ks w H1) | exact (lat_merged_one prim merge2 s I f ks w H2)].
  - intros f m ks a b Hkind [Ha1 [Haok Ha2]] [Hb1 [Hbok Hb2]].
    split; [exact (lat_merged_merge prim merge1 s I f m ks a b Hkind Ha1 Hb1) |].
    split; [exact (keeps f m a b Hkind Haok Hbok) |].
    rewrite (agree f m a b Hkind Haok Hbok).
    exact (lat_merged_merge prim merge2 s I f m ks a b Hkind Ha2 Hb2).
  - intros c e r args vs Hin Hhead Hbody Hvs.
    split; apply (lat_derived_clause _ _ s I c e r args vs Hin Hhead); try exact Hvs;
      apply lat_body_intro; refine (Forall_impl _ _ Hbody); intros p;
      apply premise_lat_in_impl; intros *; tauto.
  - intros c e f args v ks w Hin Hhead Hbody Hks Hw.
    split; apply (lat_assigned_clause _ _ s I c e f args v ks w Hin Hhead);
      try exact Hks; try exact Hw;
      apply lat_body_intro; refine (Forall_impl _ _ Hbody); intros p;
      apply premise_lat_in_impl; intros *; tauto.
  - split; [intros r vs H; exact (proj2 (Hrows r vs H)) |].
    split; [intros f ks w H; exact (proj2 (Hvalues f ks w H)) |].
    intros f ks w H. exact (proj2 (proj2 (Hmerged f ks w H))).
Qed.

(** The meaning with [merge2] is contained in the meaning with [merge1], and a value that a read
    sees with [merge2] is a value of [ok]. *)
Lemma lat_merge_backward :
  (forall r vs, lat_derived prim merge2 s I r vs -> lat_derived prim merge1 s I r vs) /\
  (forall f ks w, lat_assigned prim merge2 s I f ks w -> lat_assigned prim merge1 s I f ks w) /\
  (forall f ks w, lat_merged prim merge2 s I f ks w -> lat_merged prim merge1 s I f ks w).
Proof.
  destruct (lat_least prim merge2 s I (lat_derived prim merge1 s I)
    (lat_assigned prim merge1 s I) (fun f ks w => ok f w /\ lat_merged prim merge1 s I f ks w))
    as [Hrows [Hvalues Hmerged]].
  - intros r vs Hin HI. apply lat_derived_input; assumption.
  - intros f ks w Hw.
    split; [exact (assigned_ok f ks w Hw) | exact (lat_merged_one prim merge1 s I f ks w Hw)].
  - intros f m ks a b Hkind [Haok Ha] [Hbok Hb].
    rewrite <- (agree f m a b Hkind Haok Hbok).
    split; [exact (keeps f m a b Hkind Haok Hbok) |].
    exact (lat_merged_merge prim merge1 s I f m ks a b Hkind Ha Hb).
  - intros c e r args vs Hin Hhead Hbody Hvs.
    apply (lat_derived_clause prim merge1 s I c e r args vs Hin Hhead); [| exact Hvs].
    apply lat_body_intro. refine (Forall_impl _ _ Hbody). intros p.
    apply premise_lat_in_impl; intros *; tauto.
  - intros c e f args v ks w Hin Hhead Hbody Hks Hw.
    apply (lat_assigned_clause prim merge1 s I c e f args v ks w Hin Hhead);
      [| exact Hks | exact Hw].
    apply lat_body_intro. refine (Forall_impl _ _ Hbody). intros p.
    apply premise_lat_in_impl; intros *; tauto.
  - split; [exact Hrows |].
    split; [exact Hvalues |].
    intros f ks w H. exact (proj2 (Hmerged f ks w H)).
Qed.

End Moves.

(** The meaning depends on the merge only at the codes of the lattice tables, and at each
    lattice table [f] only at the values of [ok f], when [ok f] holds of every value that the
    clauses assign at [f] with [merge1] and the merge keeps it. *)
Lemma lat_merge_agrees_at {V : Type} (prim : positive -> list V -> option V)
    (merge1 merge2 : positive -> V -> V -> V) (ok : positive -> V -> Prop) (s : spec V)
    (I : positive -> list V -> Prop) :
  (forall f m a b, lookup_kind (tables s) f = Some (OLat m) -> ok f a -> ok f b ->
    merge1 m a b = merge2 m a b) ->
  (forall f m a b, lookup_kind (tables s) f = Some (OLat m) -> ok f a -> ok f b ->
    ok f (merge1 m a b)) ->
  (forall f ks w, lat_assigned prim merge1 s I f ks w -> ok f w) ->
  (forall r vs, lat_derived prim merge1 s I r vs <-> lat_derived prim merge2 s I r vs) /\
  (forall f ks w, lat_assigned prim merge1 s I f ks w <-> lat_assigned prim merge2 s I f ks w) /\
  (forall f ks w, lat_merged prim merge1 s I f ks w <-> lat_merged prim merge2 s I f ks w).
Proof.
  intros Hagree Hkeeps Hok.
  destruct (lat_merge_forward prim merge1 merge2 ok s I Hagree Hkeeps Hok)
    as [Hrows [Hvalues Hmerged]].
  destruct (lat_merge_backward prim merge1 merge2 ok s I Hagree Hkeeps Hok)
    as [Hrows' [Hvalues' Hmerged']].
  split; [intros r vs; split; [apply Hrows | apply Hrows'] |].
  split; [intros f ks w; split; [apply Hvalues | apply Hvalues'] |].
  intros f ks w; split; [apply Hmerged | apply Hmerged'].
Qed.

(** * Merges at every code *)

(** [Pos.max] at every code, with no join. *)
Module MaxMergeCode <: MERGE_OPS.
  Definition merge (_ a b : positive) : positive := Pos.max a b.
End MaxMergeCode.

Module MaxMerge (P : PRIMITIVES) <: MERGE P.
  Include MaxMergeCode.

  Definition codes : list positive := [].

  Definition encoded (_ _ : positive) : Prop := True.

  Lemma merge_comm : forall m a b, merge m a b = merge m b a.
  Proof.
    intros m a b. apply Pos.max_comm.
  Qed.

  Lemma merge_assoc : forall m a b c, merge m a (merge m b c) = merge m (merge m a b) c.
  Proof.
    intros m a b c. apply Pos.max_assoc.
  Qed.

  Lemma merge_idem : forall m a, merge m a a = a.
  Proof.
    intros m a. apply Pos.max_id.
  Qed.

  Lemma merge_agrees : forall m a b, In m codes -> encoded m a -> encoded m b ->
    merge m a b = prim_merge P.prim m a b.
  Proof.
    intros m a b [].
  Qed.

  Lemma prim_merge_encoded : forall m a b, In m codes -> encoded m a -> encoded m b ->
    encoded m (prim_merge P.prim m a b).
  Proof.
    intros m a b [].
  Qed.
End MaxMerge.

(** The merge [B], with the join [D] of the values of [E] at the code of [D]. *)
Module DecodedMergeCode (B : MERGE_OPS) (E : ENCODE) (D : DECODED_OPS E) <: MERGE_OPS.
  Definition merge (m a b : positive) : positive :=
    if Pos.eqb m D.code then lift_merge E.encode E.decode D.join a b else B.merge m a b.
End DecodedMergeCode.

Module DecodedMerge (P : PRIMITIVES) (B : MERGE P) (E : ENCODE) (D : DECODED P E) <: MERGE P.
  Include DecodedMergeCode B E D.

  Definition codes : list positive := D.code :: B.codes.

  Definition encoded (m v : positive) : Prop :=
    if Pos.eqb m D.code then exists x, v = E.encode x else B.encoded m v.

  (** At the code of the join, the merge is the lifted join. *)
  Lemma merge_code : forall a b, merge D.code a b = lift_merge E.encode E.decode D.join a b.
  Proof.
    intros a b. unfold merge. rewrite Pos.eqb_refl. reflexivity.
  Qed.

  (** At another code, the merge is the merge of [B]. *)
  Lemma merge_other : forall m a b, m <> D.code -> merge m a b = B.merge m a b.
  Proof.
    intros m a b Hm. unfold merge.
    destruct (Pos.eqb_spec m D.code) as [Heq | _]; [contradiction | reflexivity].
  Qed.

  (** The engine values at the code of the join are the encodings of [E]. *)
  Lemma encoded_code : forall v, encoded D.code v <-> exists x, v = E.encode x.
  Proof.
    intros v. unfold encoded. rewrite Pos.eqb_refl. reflexivity.
  Qed.

  (** On encodings, the merge of the primitives at the code encodes the join. *)
  Lemma prim_merge_code : forall x y,
    prim_merge P.prim D.code (E.encode x) (E.encode y) = E.encode (D.join x y).
  Proof.
    intros x y. unfold prim_merge. rewrite D.prim_join. reflexivity.
  Qed.

  (** On encodings, the merge at the code agrees with the merge of the primitives. *)
  Lemma merge_agrees_code : forall x y,
    merge D.code (E.encode x) (E.encode y) = prim_merge P.prim D.code (E.encode x) (E.encode y).
  Proof.
    intros x y.
    rewrite merge_code, prim_merge_code.
    exact (lift_merge_encode E.encode E.decode D.join E.decode_encode x y).
  Qed.

  Lemma merge_comm : forall m a b, merge m a b = merge m b a.
  Proof.
    intros m a b. unfold merge.
    destruct (Pos.eqb m D.code).
    - exact (lift_merge_comm E.encode E.decode D.join D.join_comm a b).
    - apply B.merge_comm.
  Qed.

  Lemma merge_assoc : forall m a b c, merge m a (merge m b c) = merge m (merge m a b) c.
  Proof.
    intros m a b c. unfold merge.
    destruct (Pos.eqb m D.code).
    - exact (lift_merge_assoc E.encode E.decode D.join E.decode_encode D.join_assoc a b c).
    - apply B.merge_assoc.
  Qed.

  Lemma merge_idem : forall m a, merge m a a = a.
  Proof.
    intros m a. unfold merge.
    destruct (Pos.eqb m D.code).
    - exact (lift_merge_idem E.encode E.decode D.join D.join_idem a).
    - apply B.merge_idem.
  Qed.

  Lemma merge_agrees : forall m a b, In m codes -> encoded m a -> encoded m b ->
    merge m a b = prim_merge P.prim m a b.
  Proof.
    intros m a b Hin.
    unfold encoded, merge.
    destruct (Pos.eqb_spec m D.code) as [Hm | Hm]; intros Ha Hb.
    - subst m.
      destruct Ha as [x Hx], Hb as [y Hy].
      subst a b.
      rewrite (lift_merge_encode E.encode E.decode D.join E.decode_encode x y).
      symmetry. apply prim_merge_code.
    - destruct Hin as [Hin | Hin]; [congruence |].
      exact (B.merge_agrees m a b Hin Ha Hb).
  Qed.

  Lemma prim_merge_encoded : forall m a b, In m codes -> encoded m a -> encoded m b ->
    encoded m (prim_merge P.prim m a b).
  Proof.
    intros m a b Hin.
    unfold encoded.
    destruct (Pos.eqb_spec m D.code) as [Hm | Hm]; intros Ha Hb.
    - subst m.
      destruct Ha as [x Hx], Hb as [y Hy].
      subst a b.
      exists (D.join x y). apply prim_merge_code.
    - destruct Hin as [Hin | Hin]; [congruence |].
      exact (B.prim_merge_encoded m a b Hin Ha Hb).
  Qed.
End DecodedMerge.

(** * Value modules *)

(** The engine values of positives, with the primitives of [P] and the merge [M]. *)
Module MergeValueCode (P : PRIMITIVES) (M : MERGE_OPS) <: VALUE_OPS.
  Include PosKeyCode.
  Definition prim := P.prim.
  Definition merge := M.merge.
End MergeValueCode.

Module MergeValue (P : PRIMITIVES) (M : MERGE P) <: VALUE.
  Include MergeValueCode P M.
  Include VALUE_SPEC.

  Lemma encode_inj : forall a b, encode a = encode b -> a = b.
  Proof.
    intros a b Hab. exact Hab.
  Qed.

  Lemma eqb_spec : forall a b, reflect (a = b) (eqb a b).
  Proof.
    exact Pos.eqb_spec.
  Qed.

  Lemma merge_comm : forall m a b, merge m a b = merge m b a.
  Proof.
    exact M.merge_comm.
  Qed.

  Lemma merge_assoc : forall m a b c, merge m a (merge m b c) = merge m (merge m a b) c.
  Proof.
    exact M.merge_assoc.
  Qed.

  Lemma merge_idem : forall m a, merge m a a = a.
  Proof.
    exact M.merge_idem.
  Qed.

  (** The meaning of a specification with the primitives of [P] is the same with the merge of
      the primitives and with [merge], when every lattice table merges at a code of [M] and
      every value that the clauses assign at a table is an encoding at the code of its merge. *)
  Lemma lat_merge_moves : forall (s : spec positive) (I : positive -> list positive -> Prop),
    (forall f m, lookup_kind (tables s) f = Some (OLat m) -> In m M.codes) ->
    (forall f m ks w, lookup_kind (tables s) f = Some (OLat m) ->
      lat_assigned P.prim (prim_merge P.prim) s I f ks w -> M.encoded m w) ->
    (forall r vs,
      lat_derived P.prim (prim_merge P.prim) s I r vs <-> lat_derived P.prim merge s I r vs) /\
    (forall f ks w,
      lat_assigned P.prim (prim_merge P.prim) s I f ks w <->
        lat_assigned P.prim merge s I f ks w) /\
    (forall f ks w,
      lat_merged P.prim (prim_merge P.prim) s I f ks w <-> lat_merged P.prim merge s I f ks w).
  Proof.
    intros s I Hcodes Hassigned.
    apply (lat_merge_agrees_at P.prim (prim_merge P.prim) merge
      (fun f v => forall m, lookup_kind (tables s) f = Some (OLat m) -> M.encoded m v)).
    - intros f m a b Hkind Ha Hb. symmetry.
      exact (M.merge_agrees m a b (Hcodes f m Hkind) (Ha m Hkind) (Hb m Hkind)).
    - intros f m a b Hkind Ha Hb m' Hkind'.
      rewrite Hkind in Hkind'. injection Hkind' as Hm. subst m'.
      exact (M.prim_merge_encoded m a b (Hcodes f m Hkind) (Ha m Hkind) (Hb m Hkind)).
    - intros f ks w Hw m Hkind. exact (Hassigned f m ks w Hkind Hw).
  Qed.
End MergeValue.
