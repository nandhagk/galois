(** * Valid finite relations

    Relations use valid finite sets of tuples and inherit the may lattice.
    For example, the join of two relations contains each tuple in either input.
    Builds on: BaseCode, LatticeSet and DatalogSyntax. *)

From Stdlib Require Import List Bool PeanoNat Lia.
From Galois.Base Require Import BaseEncoding BaseCode BaseEq BaseSet.
From Galois.Lattice Require Import LatticeCore LatticeHeight LatticeSet LatticeKitFamily.
From Galois.Datalog Require Import DatalogSyntax.
Import List.ListNotations.

(** * Relation carrier and order *)

Definition tuple_encoding : encoding tuple := codec_enc (list_codec positive_codec).

(** List decoding establishes injectivity of tuple keys. *)
Theorem tuple_encoding_laws : encoding_laws tuple_encoding.
Proof.
  apply codec_laws_injective, list_codec_laws, positive_codec_laws.
Qed.

Definition relation : Type := set_t tuple_encoding.

Definition relation_lattice : lattice relation := may tuple_encoding.

(** Relation inclusion and union satisfy the weak lattice laws. *)
Theorem relation_laws : lattice_laws relation_lattice.
Proof.
  apply may_laws, tuple_encoding_laws.
Qed.

(** Relation union is a least upper bound. *)
Theorem relation_lub_laws : lub_laws relation_lattice.
Proof.
  apply may_lub, tuple_encoding_laws.
Qed.

(** Cardinality gives finite height for relations supported by a universe list. *)
Theorem relation_height_on (universe : list tuple) :
  height_on relation_lattice (within_set tuple_encoding universe).
Proof.
  apply may_height, tuple_encoding_laws.
Defined.

(** Relation membership observes the public finite-set representation. *)
Definition member ts (r : relation) := FinSet.mem tuple_encoding ts (set_raw r).

(** Relation inclusion is implication between tuple memberships. *)
Theorem relation_leb s t :
  leb relation_lattice s t = true <-> forall ts, member ts s = true -> member ts t = true.
Proof.
  apply may_leb, tuple_encoding_laws.
Qed.

(** The empty relation contains no tuple. *)
Theorem relation_bot ts : member ts (bot relation_lattice) = false.
Proof.
  exact (family_bot (may_family tuple_encoding tuple_encoding_laws) ts).
Qed.

(** Relation join is pointwise disjunction of tuple memberships. *)
Theorem relation_join ts s t :
  member ts (join relation_lattice s t) = (member ts s || member ts t)%bool.
Proof.
  exact (family_join (may_family tuple_encoding tuple_encoding_laws) ts s t).
Qed.

(** List construction keeps exactly its listed tuples. *)
Theorem relation_of_list ts xs :
  member ts (set_of_list tuple_encoding xs) = true <-> In ts xs.
Proof.
  unfold member; rewrite set_of_list_raw, FinSet.mem_of_list, existsb_exists.
  split.
  - intros [us [Hin Heq]]; apply (eqb_true_iff _ tuple_encoding_laws) in Heq.
    subst us; exact Hin.
  - intro Hin; exists ts; split; [exact Hin | apply eqb_refl].
Qed.

Definition atom_constants {P} (a : atom P) : tuple :=
  flat_map (fun t => match t with TVar _ => [] | TConst c => [c] end) (args a).

(** The finite alphabet contains all source constants, including constants in facts. *)
Definition constants {P} (prog : program P) (facts : list (ground_atom P)) : tuple :=
  flat_map (fun r => atom_constants (head r) ++
    flat_map (fun l => atom_constants (lit_atom l)) (body r)) (rules prog) ++
  flat_map snd facts.

Fixpoint tuple_words (n : nat) (cs : tuple) : list tuple :=
  match n with
  | 0 => [[]]
  | S n' => flat_map (fun c => map (cons c) (tuple_words n' cs)) cs
  end.

Lemma tuple_words_spec n cs ts :
  In ts (tuple_words n cs) <-> length ts = n /\ forall c, In c ts -> In c cs.
Proof.
  revert ts; induction n as [|n IH]; intros [|c ts]; cbn [tuple_words].
  - cbn; intuition.
  - cbn; split.
    + intros [Hbad | Hbad]; [discriminate | contradiction].
    + intros [Hbad _]; discriminate.
  - rewrite in_flat_map; split.
    + intros [c [Hin Hbad]]; apply in_map_iff in Hbad.
      destruct Hbad as [ts [Hbad _]]; discriminate.
    + intros [Hbad _]; discriminate.
  - rewrite in_flat_map; split.
    + intros [c' [Hc Hmap]]; apply in_map_iff in Hmap.
      destruct Hmap as [ts' [Heq Hts]]; injection Heq as Heqc Heqt; subst c' ts'.
      apply IH in Hts; cbn; destruct Hts as [Hlen Hin]; split; [lia |].
      intros d [Heq | Hd]; [subst d; exact Hc | apply Hin, Hd].
    + intros [Hlen Hin]; exists c; split; [apply Hin; now left |].
      apply in_map_iff; exists ts; split; [reflexivity | apply IH].
      cbn in Hlen; split; [lia | intros d Hd; apply Hin; now right].
Qed.

(** Source head and fact lengths give a finite support independent of predicate encoding. *)
Definition arities {P} (prog : program P) (facts : list (ground_atom P)) :=
  map (fun r => length (args (head r))) (rules prog) ++ map (fun f => length (snd f)) facts.

(** The proof-only universe lists tuples of source head or fact lengths over the alphabet. *)
Definition universe {P} (prog : program P) (facts : list (ground_atom P)) : list tuple :=
  flat_map (fun n => tuple_words n (constants prog facts)) (arities prog facts).

(** Universe membership separates tuple length from membership in the source alphabet. *)
Theorem universe_spec {P} (prog : program P) facts ts :
  In ts (universe prog facts) <->
    In (length ts) (arities prog facts) /\
    forall c, In c ts -> In c (constants prog facts).
Proof.
  unfold universe; rewrite in_flat_map; split.
  - intros [n [Hn Hts]]; apply tuple_words_spec in Hts as [Hlen Hcs].
    subst n; auto.
  - intros [Hlen Hcs]; exists (length ts); split; [exact Hlen |].
    apply tuple_words_spec; auto.
Qed.

(** Every source fact has finite universe support. *)
Theorem fact_universe {P} (prog : program P) facts f :
  In f facts -> In (snd f) (universe prog facts).
Proof.
  intro Hfact; apply universe_spec; split.
  - unfold arities; apply in_app_iff; right; apply in_map_iff; exists f; auto.
  - intros c Hc; unfold constants; apply in_app_iff; right.
    apply in_flat_map; exists f; auto.
Qed.

(** Safety obtains every variable-valued head constant from a positive body tuple. *)
Theorem head_universe {P} (prog : program P) facts r sigma :
  safe_rule r -> In r (rules prog) ->
  (forall a, In (LPos a) (body r) ->
    In (map (inst sigma) (args a)) (universe prog facts)) ->
  In (map (inst sigma) (args (head r))) (universe prog facts).
Proof.
  intros Hsafe Hr Hpos; apply universe_spec; split.
  - rewrite length_map; unfold arities; apply in_app_iff; left.
    apply in_map_iff; exists r; auto.
  - intros c Hc; apply in_map_iff in Hc as [[v | d] [Heq Hterm]].
    + cbn [inst] in Heq; subst c.
      assert (Hv : In v (atom_vars (head r))) by (apply atom_vars_spec, Hterm).
      destruct (Hsafe v (or_introl Hv)) as [a [Ha Hva]].
      pose proof (proj2 (proj1 (universe_spec prog facts _) (Hpos a Ha))) as Hcs.
      apply Hcs; apply in_map_iff; exists (TVar v); split; [reflexivity |].
      apply atom_vars_spec, Hva.
    + cbn [inst] in Heq; subst c; unfold constants; apply in_app_iff; left.
      apply in_flat_map; exists r; split; [exact Hr |].
      apply in_app_iff; left; unfold atom_constants; apply in_flat_map.
      exists (TConst d); cbn; auto.
Qed.
