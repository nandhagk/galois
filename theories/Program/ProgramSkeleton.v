(** * Structured syntax and positions

    Binary statements use relative labels and root-outward positions.
    For example, [DBody] selects the body of a block.
    Builds on: BaseCode and CostMonad. *)

From Stdlib Require Import List Bool Arith Lia PArith.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseCode.
Import List.ListNotations Cost.Notations.

Module Skeleton.

(** Statements separate client atoms and guards from structured control. *)
Inductive stmt (A G : Type) : Type :=
  | Atom (a : A)
  | Seq (s1 s2 : stmt A G)
  | If (g : G) (s1 s2 : stmt A G)
  | Block (s : stmt A G)
  | Loop (s : stmt A G)
  | Jump (n : nat)
  | JumpIf (g : G) (n : nat)
  | JumpTable (g : G) (ns : list nat) (n : nat).
Arguments Atom {A G}.
Arguments Seq {A G}.
Arguments If {A G}.
Arguments Block {A G}.
Arguments Loop {A G}.
Arguments Jump {A G}.
Arguments JumpIf {A G}.
Arguments JumpTable {A G}.

End Skeleton.
Import Skeleton.

(** Directions select binary children or the body of a labelled statement. *)
Inductive dir : Type :=
  | DFirst
  | DSecond
  | DBody.

(** Positions list directions from the root outwards. *)
Definition position : Type := list dir.

(** Direction conversion is a constant-size primitive. *)
Definition dir_to_code (d : dir) : Cost.t code :=
  Cost.ret (BaseCode.Atom
    (match d with DFirst => 1%positive | DSecond => 2%positive | DBody => 3%positive end)).

(** Direction decoding rejects every other tag and tree shape. *)
Definition dir_of_code (c : code) : option dir :=
  match c with
  | BaseCode.Atom xH => Some DFirst
  | BaseCode.Atom (xO xH) => Some DSecond
  | BaseCode.Atom (xI xH) => Some DBody
  | _ => None
  end.

(** Every direction is recovered by its decoder. *)
Theorem dir_roundtrip d : dir_of_code (Cost.value (dir_to_code d)) = Some d.
Proof.
  destruct d; reflexivity.
Qed.

Definition dir_codec := derive dir_to_code dir_of_code dir_roundtrip.
Definition dir_encoding := codec_enc dir_codec.
Definition position_codec := list_codec dir_codec.
Definition position_encoding := codec_enc position_codec.

(** Direction codes are injective independently of computational data. *)
Theorem dir_encoding_laws : encoding_laws dir_encoding.
Proof.
  apply codec_laws_injective, derive_laws.
Qed.

(** Ordered position codes distinguish every direction list. *)
Theorem position_encoding_laws : encoding_laws position_encoding.
Proof.
  apply codec_laws_injective, list_codec_laws, derive_laws.
Qed.

(** A direction exists only for the corresponding statement shape. *)
Definition child {A G} (s : stmt A G) (d : dir) : option (stmt A G) :=
  match s, d with
  | Seq s1 _, DFirst | If _ s1 _, DFirst => Some s1
  | Seq _ s2, DSecond | If _ _ s2, DSecond => Some s2
  | Block s, DBody | Loop s, DBody => Some s
  | _, _ => None
  end.

(** Lookup follows a position and rejects a missing child. *)
Fixpoint sub {A G} (s : stmt A G) (p : position) : option (stmt A G) :=
  match p with
  | [] => Some s
  | d :: p =>
    match child s d with
    | Some c => sub c p
    | None => None
    end
  end.

(** Valid positions occur once, in preorder. *)
Fixpoint positions {A G} (s : stmt A G) : list position :=
  match s with
  | Seq s1 s2 | If _ s1 s2 =>
    [] :: map (cons DFirst) (positions s1) ++ map (cons DSecond) (positions s2)
  | Block s | Loop s => [] :: map (cons DBody) (positions s)
  | _ => [[]]
  end.

(** Every relative label must refer to an enclosing block or loop. *)
Fixpoint labels_ok {A G} (d : nat) (s : stmt A G) : bool :=
  match s with
  | Seq s1 s2 | If _ s1 s2 => labels_ok d s1 && labels_ok d s2
  | Block s | Loop s => labels_ok (S d) s
  | Jump n | JumpIf _ n => n <? d
  | JumpTable _ ns n => forallb (fun n => n <? d) ns && (n <? d)
  | Atom _ => true
  end.

(** Position concatenation composes successful lookups and preserves failures. *)
Theorem sub_app {A G} (s : stmt A G) p q :
  sub s (p ++ q) =
    match sub s p with
    | Some t => sub t q
    | None => None
    end.
Proof.
  revert s; induction p as [|d p IH]; intro s; cbn; [reflexivity|].
  destruct (child s d); [apply IH|reflexivity].
Qed.

(** A single appended direction selects the located owner's child. *)
Theorem sub_child {A G} (s : stmt A G) p t d :
  sub s p = Some t -> sub s (p ++ [d]) = child t d.
Proof.
  intro Hsub; rewrite sub_app, Hsub; cbn; destruct (child t d); reflexivity.
Qed.

Local Lemma nodup_cons_map (d : dir) (xs : list position) :
  NoDup xs -> NoDup (map (cons d) xs).
Proof.
  intro Hnodup; induction Hnodup as [|x xs Hnot Hnodup IH]; cbn; constructor.
  - intro Hin; apply in_map_iff in Hin; destruct Hin as [y [Heq Hin]].
    inversion Heq; subst; contradiction.
  - exact IH.
Qed.

Local Lemma positions_nodup_binary d e (xs ys : list position) :
  d <> e -> NoDup xs -> NoDup ys ->
  NoDup ([] :: map (cons d) xs ++ map (cons e) ys).
Proof.
  intros Hne Hxs Hys; constructor.
  - intro Hin; apply in_app_or in Hin; destruct Hin as [Hin|Hin];
      apply in_map_iff in Hin; destruct Hin as [p [Hbad _]]; discriminate.
  - apply NoDup_app; repeat split.
    + apply nodup_cons_map; exact Hxs.
    + apply nodup_cons_map; exact Hys.
    + intros p Hin Hin'; apply in_map_iff in Hin; apply in_map_iff in Hin'.
      destruct Hin as [q [Heq _]], Hin' as [r [Heq' _]]; congruence.
Qed.

(** The position enumeration contains exactly the valid positions, without duplicates. *)
Theorem positions_exact {A G} (prog : stmt A G) :
  NoDup (positions prog) /\
  (forall p, In p (positions prog) <-> exists s, sub prog p = Some s).
Proof.
  induction prog as [a|s1 [H1 E1] s2 [H2 E2]|g s1 [H1 E1] s2 [H2 E2]|
    s [H E]|s [H E]|n|g n|g ns n]; split.
  all: try solve [cbn; constructor; [tauto|constructor]].
  all: try solve [apply positions_nodup_binary; [discriminate|exact H1|exact H2]].
  all: try solve [cbn; constructor; [intro Hin; apply in_map_iff in Hin;
    destruct Hin as [p [Hbad _]]; discriminate|apply nodup_cons_map; exact H]].
  all: intros [|d p]; cbn; try solve [split; [intros _; eexists; reflexivity|tauto]].
  all: try solve [destruct d; cbn; split; [tauto|intros [? Hbad]; discriminate]].
  all: rewrite ?in_app_iff, ?in_map_iff.
  all: destruct d; cbn.
  all: try solve [split; [intros [Hbad|Hbad]; [discriminate|];
    destruct Hbad as [q [Hbad _]]; discriminate|intros [? Hbad]; discriminate]].
  all: split.
  all: try solve [intros [Hbad|Hin]; [discriminate|];
    destruct Hin as [[q [Heq Hin]]|[q [Heq Hin]]]; inversion Heq; subst;
    first [apply E1|apply E2]; exact Hin].
  all: try solve [intro Hex; first [apply E1 in Hex|apply E2 in Hex];
    right; first [left; exists p|right; exists p]; split; [reflexivity|exact Hex]].
  all: try solve [intros [Hbad|[q [Heq Hin]]]; [discriminate|]; inversion Heq; subst;
    apply E; exact Hin].
  all: try solve [intro Hex; apply E in Hex; right; exists p; split; [reflexivity|exact Hex]].
  all: try solve [intros [Hbad|Hfalse]; [discriminate|contradiction]].
  all: try solve [intros [? Hbad]; discriminate].
  all: try solve [intro Hex; right; right; exists p; split; [reflexivity|];
    apply (proj2 (E2 p)); exact Hex].
Qed.
