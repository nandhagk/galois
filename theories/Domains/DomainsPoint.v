(** * Singleton payloads

    Singleton payloads evaluate through the empty transfer table.
    For example, adding two singleton operands computes the wrapped singleton result.
    Builds on: DomainsNumeric and DomainsTransfer. *)

From Stdlib Require Import ZArith List Bool.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Lattice Require Import LatticeCore.
From Galois.Bits Require Import BitsWord BitsOp.
From Galois.Domains Require Import DomainsNumeric DomainsTransfer.
Import List.ListNotations Cost.Notations.

(** Payloads distinguish impossible, exact and unrestricted integers. *)
Inductive point : Type :=
  | PBot
  | PVal (z : Z)
  | PTop.

Definition point_le (a b : point) : bool :=
  match a, b with
  | PBot, _ => true
  | _, PTop => true
  | PVal x, PVal y => Z.eqb x y
  | _, _ => false
  end.

Definition point_join (a b : point) : point :=
  match a, b with
  | PBot, _ => b
  | _, PBot => a
  | PVal x, PVal y => if Z.eqb x y then a else PTop
  | _, _ => PTop
  end.

Definition point_meet (a b : point) : point :=
  match a, b with
  | PTop, _ => b
  | _, PTop => a
  | PVal x, PVal y => if Z.eqb x y then a else PBot
  | _, _ => PBot
  end.

Definition point_lattice : lattice point := simple point_le PBot point_join.

Local Lemma point_le_equation a b : leb point_lattice a b = point_le a b.
Proof.
  reflexivity.
Qed.

(** A singleton denotes its integer independently of the width validity predicate. *)
Definition point_gamma (_ : width) (p : point) (z : Z) : Prop :=
  match p with
  | PBot => False
  | PVal x => x = z
  | PTop => True
  end.

(** The flat singleton order satisfies the weak lattice laws. *)
Theorem point_lattice_laws : lattice_laws point_lattice.
Proof.
  apply simple_laws.
  - intros [|z|]; cbn [point_le]; auto using Z.eqb_refl.
  - intros [|x|] [|y|] [|z|]; cbn [point_le]; intros Hxy Hyz;
      try discriminate; try reflexivity.
    apply Z.eqb_eq in Hxy. apply Z.eqb_eq in Hyz. subst. apply Z.eqb_refl.
  - intros []; reflexivity.
  - intros [|x|] [|y|]; cbn [point_le point_join]; try reflexivity;
      rewrite ?Z.eqb_refl; try reflexivity.
    destruct (Z.eqb x y); cbn [point_le]; auto using Z.eqb_refl.
  - intros [|x|] [|y|]; cbn [point_le point_join]; try reflexivity;
      rewrite ?Z.eqb_refl; try reflexivity.
    destruct (Z.eqb x y) eqn:Hxy; cbn [point_le]; [|reflexivity].
    apply Z.eqb_eq in Hxy. subst. apply Z.eqb_refl.
Qed.

Definition point_shape : Transfer.shape (width * point) point op width word :=
  {| Transfer.eval_c := fun o xs => Cost.step ;; Cost.ret (eval_op o xs);
     Transfer.point_c := fun wp =>
       Cost.step ;; Cost.ret
         (match snd wp with
          | PVal z => Some (fst wp, z)
          | _ => None
          end);
     Transfer.is_empty_c := fun wp =>
       Cost.step ;; Cost.ret (match snd wp with PBot => true | _ => false end);
     Transfer.inj_c := fun _ c => Cost.step ;; Cost.ret (PVal (snd c));
     Transfer.bot_out := fun _ => PBot;
     Transfer.top_out := fun _ => PTop;
     Transfer.keep_c := fun wp => Cost.ret (snd wp) |}.

(** The reference dictionary needs no operator-specific table entry. *)
Definition point_word_domain : word_domain point :=
  word_of_table empty_table point_shape (fun _ => point_lattice) (fun _ => PTop)
    (fun w z => Cost.step ;; Cost.ret (PVal (wrap w z)))
    (fun _ a b => Cost.step ;; Cost.ret (point_meet a b)).

Local Lemma point_shape_laws :
  transfer_sem point_shape (payload_sound point_gamma) (word_output point_gamma) word_context.
Proof.
  constructor.
  - intros [w [|z|]] [v x] [u y] Hp Hg; try discriminate.
    inversion Hp; subst. destruct Hg as [Hwidth [Hword Hval]].
    cbn in Hwidth, Hval. subst. reflexivity.
  - intros [w [|z|]] c Hempty Hg; try discriminate.
    exact (proj2 (proj2 Hg)).
  - intros r [w z] Hctx. reflexivity.
  - intros r c H. exact H.
  - intros r c Hctx. exact I.
  - intros r [w p] [v z] [Hwidth [Hword Hp]]. cbn in *.
    subst w. exact Hp.
Qed.

Local Lemma point_table_laws :
  table_laws (@empty_table (width * point) point op width) point_shape
    (payload_sound point_gamma) (word_output point_gamma) word_context.
Proof.
  constructor; intros; discriminate.
Qed.

Local Lemma point_mono w a b z :
  leb point_lattice a b = true -> point_gamma w a z -> point_gamma w b z.
Proof.
  change (point_le a b = true -> point_gamma w a z -> point_gamma w b z).
  destruct a as [|x|], b as [|y|]; cbn [point_le point_gamma];
    intros Hle Ha; try contradiction; try discriminate; try exact I.
  apply Z.eqb_eq in Hle. congruence.
Qed.

(** The reference word dictionary obtains all transfer soundness from the shared harness. *)
Theorem point_word_laws : word_laws point_word_domain point_gamma.
Proof.
  apply word_of_table_laws.
  - intros. reflexivity.
  - exact point_shape_laws.
  - exact point_table_laws.
  - intros. exact point_lattice_laws.
  - exact point_mono.
  - intros w z H. exact H.
  - intros. exact I.
  - intros. reflexivity.
  - constructor.
    + intros [w p]. apply (leb_refl point_lattice_laws).
    + intros k n f r a xs Hf. discriminate Hf.
  - intros w [|x|] [|y|] z Ha Hb; cbn [point_meet point_gamma] in *;
      try contradiction; try exact I; try assumption.
    subst x y. rewrite Z.eqb_refl. reflexivity.
  - intros w [|x|] [|y|]; cbn [point_meet]; try reflexivity;
      rewrite point_le_equation; cbn [point_le]; try reflexivity.
    destruct (Z.eqb x y); cbn [point_le]; auto using Z.eqb_refl.
    all: try rewrite Z.eqb_refl; try reflexivity.
    all: autorewrite with galois_cost; cbn [point_le]; rewrite Z.eqb_refl; reflexivity.
Qed.
