(** * Persistent union-find forests

    Parent links increase rank, bounding traversal by the cached maximum rank.
    For example, union of two unknown keys creates one class and find compresses its paths.
    Builds on: BaseEncoding, BaseEq, BaseMap and CostMonad. *)

From Stdlib Require Import List Bool NArith PeanoNat Lia Relation_Definitions Relation_Operators
  Sorting.Sorted.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap.
Import List.ListNotations Cost.Notations.

Module UnionFind.

(** A forest stores parent and rank maps with a global rank bound. *)
Record t (K : Type) : Type := Forest {
  parents : Map.t K K;
  ranks : Map.t K nat;
  max_rank : nat
}.

Arguments Forest {K}.
Arguments parents {K}.
Arguments ranks {K}.
Arguments max_rank {K}.

(** The empty forest regards every key, including an unknown key, as its own root. *)
Definition make_c {K} : Cost.t (t K) :=
  let* p := Map.empty_c in
  let* r := Map.empty_c in
  Cost.ret (Forest p r 0).
Definition make {K} : t K := Cost.value make_c.

(** Missing rank entries have rank zero. *)
Definition rank_of_c {K} (E : encoding K) (uf : t K) (x : K) : Cost.t nat :=
  Cost.map (fun o =>
    match o with
    | Some n => n
    | None => 0
    end) (Map.get_c E x (ranks uf)).
Definition rank_of {K} (E : encoding K) (uf : t K) (x : K) :=
  Cost.value (rank_of_c E uf x).

(** Both stored maps are well formed and every parent has strictly larger bounded rank. *)
Definition wf {K} (E : encoding K) (uf : t K) : Prop :=
  Map.wf E (parents uf) /\ Map.wf E (ranks uf) /\
  (forall x, rank_of E uf x <= max_rank uf) /\
  (forall x y, Map.get E x (parents uf) = Some y -> rank_of E uf x < rank_of E uf y).

(** Redirect changes one parent without changing ranks. *)
Definition redirect_c {K} (E : encoding K) (x root : K) (uf : t K) : Cost.t (t K) :=
  let* p := Map.set_c E x root (parents uf) in
  Cost.ret (Forest p (ranks uf) (max_rank uf)).
Definition redirect {K} (E : encoding K) (x root : K) (uf : t K) :=
  Cost.value (redirect_c E x root uf).

(** Exhaustion returns the current key and compresses the traversed prefix to that key.
    Root correctness requires enough fuel and a well-formed forest. *)
Fixpoint find_fuel_c {K} (E : encoding K) (fuel : nat) (x : K) (uf : t K)
    : Cost.t (K * t K) :=
  match fuel with
  | 0 => Cost.ret (x, uf)
  | S rest =>
    Cost.step ;;
    let* parent := Map.get_c E x (parents uf) in
    match parent with
    | None => Cost.ret (x, uf)
    | Some y =>
      let* result := find_fuel_c E rest y uf in
      let '(root, compressed) := result in
      let* uf' := redirect_c E x root compressed in
      Cost.ret (root, uf')
    end
  end.
Definition find_fuel {K} (E : encoding K) fuel x (uf : t K) :=
  Cost.value (find_fuel_c E fuel x uf).

(** Rank bounds provide enough fuel on well-formed forests, even for unknown keys. *)
Definition find_c {K} (E : encoding K) (x : K) (uf : t K) : Cost.t (K * t K) :=
  find_fuel_c E (S (max_rank uf)) x uf.
Definition find {K} (E : encoding K) x (uf : t K) := Cost.value (find_c E x uf).

(** Equivalent keys have equal representatives in the original forest. *)
Definition equiv {K} (E : encoding K) (uf : t K) (x y : K) : Prop :=
  fst (find E x uf) = fst (find E y uf).

(** Touch records an isolated key without changing any rank value. *)
Definition touch_c {K} (E : encoding K) (x : K) (uf : t K) : Cost.t (t K) :=
  let* old := Map.get_c E x (ranks uf) in
  match old with
  | Some _ => Cost.ret uf
  | None =>
    let* r := Map.set_c E x 0 (ranks uf) in
    Cost.ret (Forest (parents uf) r (max_rank uf))
  end.
Definition touch {K} (E : encoding K) x (uf : t K) := Cost.value (touch_c E x uf).

(** Link joins distinct roots and optionally increments the winning root's rank. *)
Definition link_c {K} (E : encoding K) (child root : K) (raise : bool) (uf : t K)
    : Cost.t (t K) :=
  if raise then
    let* rank := rank_of_c E uf root in
    let n := S rank in
    let* p := Map.set_c E child root (parents uf) in
    let* r := Map.set_c E root n (ranks uf) in
    Cost.ret (Forest p r (Nat.max (max_rank uf) n))
  else redirect_c E child root uf.
Definition link {K} (E : encoding K) child root raise (uf : t K) :=
  Cost.value (link_c E child root raise uf).

(** Union compresses both paths and joins by rank, registering unknown arguments as needed. *)
Definition union_c {K} (E : encoding K) (x y : K) (uf : t K) : Cost.t (t K) :=
  let* first := find_c E x uf in
  let '(rx, uf1) := first in
  let* second := find_c E y uf1 in
  let '(ry, uf2) := second in
  let* same := eqb_c E rx ry in
  if same then touch_c E rx uf2
  else
    let* nx := rank_of_c E uf2 rx in
    let* ny := rank_of_c E uf2 ry in
    match Nat.compare nx ny with
    | Lt => link_c E rx ry false uf2
    | Gt => link_c E ry rx false uf2
    | Eq => link_c E ry rx true uf2
    end.
Definition union {K} (E : encoding K) x y (uf : t K) := Cost.value (union_c E x y uf).

(** Equivalence testing threads compression and rejects distinct unknown singleton classes. *)
Definition equivb_c {K} (E : encoding K) (x y : K) (uf : t K) : Cost.t (bool * t K) :=
  let* first := find_c E x uf in
  let '(rx, uf1) := first in
  let* second := find_c E y uf1 in
  let '(ry, uf2) := second in
  let* same := eqb_c E rx ry in
  Cost.ret (same, uf2).
Definition equivb {K} (E : encoding K) x y (uf : t K) := Cost.value (equivb_c E x y uf).

Local Definition known_c {K} (uf : t K) : Cost.t (Map.t K unit) :=
  Map.combine_c (fun p r => Cost.lift (fun _ => 1%N)
    (fun pr =>
      match pr with
      | (None, None) => None
      | _ => Some tt
      end) (p, r))
    (parents uf) (ranks uf).
Local Definition known {K} (uf : t K) := Cost.value (known_c uf).

Local Fixpoint firsts_c {K V} (xs : list (K * V)) : Cost.t (list K) :=
  match xs with
  | [] => Cost.ret []
  | (k, _) :: rest =>
    Cost.step ;;
    let* ks := firsts_c rest in
    Cost.ret (k :: ks)
  end.

(** Support enumerates the parent and rank domains once in canonical Map order. *)
Definition keys_c {K} (_ : encoding K) (uf : t K) : Cost.t (list K) :=
  let* m := known_c uf in
  let* xs := Map.elements_c m in firsts_c xs.
Definition keys {K} (E : encoding K) (uf : t K) := Cost.value (keys_c E uf).

Local Fixpoint unions_from_c {K} (E : encoding K) (xs : list (K * K)) (uf : t K)
    : Cost.t (t K) :=
  match xs with
  | [] => Cost.ret uf
  | (x, y) :: rest =>
    Cost.step ;;
    let* next := union_c E x y uf in unions_from_c E rest next
  end.

(** Building from unions processes pairs in input order. *)
Definition of_unions_c {K} (E : encoding K) (xs : list (K * K)) : Cost.t (t K) :=
  let* uf := make_c in unions_from_c E xs uf.
Definition of_unions {K} (E : encoding K) xs := Cost.value (of_unions_c E xs).

(** * Value equations *)

(** Construction stores two empty maps and a zero rank bound. *)
Theorem make_equation {K} : @make K = Forest Map.empty Map.empty 0.
Proof.
  reflexivity.
Qed.

(** Rank lookup returns zero on a missing binding. *)
Theorem rank_of_equation {K} (E : encoding K) uf x :
  rank_of E uf x =
  match Map.get E x (ranks uf) with
  | Some n => n
  | None => 0
  end.
Proof.
  reflexivity.
Qed.

(** Redirect uses the public Map insertion operation. *)
Theorem redirect_equation {K} (E : encoding K) x root uf :
  redirect E x root uf = Forest (Map.set E x root (parents uf)) (ranks uf) (max_rank uf).
Proof.
  reflexivity.
Qed.

(** Bounded find follows a parent and compresses on return, or stops at a root or exhaustion. *)
Theorem find_fuel_equation {K} (E : encoding K) fuel x uf :
  find_fuel E fuel x uf =
  match fuel with
  | 0 => (x, uf)
  | S rest =>
    match Map.get E x (parents uf) with
    | None => (x, uf)
    | Some y =>
      let '(root, compressed) := find_fuel E rest y uf in
      (root, redirect E x root compressed)
    end
  end.
Proof.
  destruct fuel as [|fuel]; [reflexivity|].
  unfold find_fuel at 1; cbn [find_fuel_c]; autorewrite with galois_cost.
  fold (Map.get E x (parents uf)).
  destruct (Map.get E x (parents uf)) as [y|]; [|reflexivity].
  rewrite Cost.value_bind; fold (find_fuel E fuel y uf).
  destruct (find_fuel E fuel y uf); reflexivity.
Qed.

(** Public find uses one more than the maximum rank as its traversal budget. *)
Theorem find_equation {K} (E : encoding K) x uf :
  find E x uf = find_fuel E (S (max_rank uf)) x uf.
Proof.
  reflexivity.
Qed.

(** Touch inserts a zero rank precisely when its rank binding is absent. *)
Theorem touch_equation {K} (E : encoding K) x uf :
  touch E x uf =
  match Map.get E x (ranks uf) with
  | Some _ => uf
  | None => Forest (parents uf) (Map.set E x 0 (ranks uf)) (max_rank uf)
  end.
Proof.
  unfold touch, touch_c; rewrite Cost.value_bind; fold (Map.get E x (ranks uf)).
  destruct (Map.get E x (ranks uf)); reflexivity.
Qed.

(** Raising a link updates the winning rank and its cached upper bound. *)
Theorem link_equation {K} (E : encoding K) child root raise uf :
  link E child root raise uf =
  if raise then
    let n := S (rank_of E uf root) in
    Forest (Map.set E child root (parents uf)) (Map.set E root n (ranks uf))
      (Nat.max (max_rank uf) n)
  else redirect E child root uf.
Proof.
  destruct raise; reflexivity.
Qed.

(** Union's value follows the legacy rank comparison and left-root tie break. *)
Theorem union_equation {K} (E : encoding K) x y uf :
  union E x y uf =
  let '(rx, uf1) := find E x uf in
  let '(ry, uf2) := find E y uf1 in
  if eqb E rx ry then touch E rx uf2
  else
    match Nat.compare (rank_of E uf2 rx) (rank_of E uf2 ry) with
    | Lt => link E rx ry false uf2
    | Gt => link E ry rx false uf2
    | Eq => link E ry rx true uf2
    end.
Proof.
  unfold union, union_c; rewrite Cost.value_bind; fold (find E x uf).
  destruct (find E x uf) as [rx u1].
  rewrite Cost.value_bind; fold (find E y u1).
  destruct (find E y u1) as [ry u2].
  rewrite Cost.value_bind; fold (eqb E rx ry).
  destruct (eqb E rx ry); [reflexivity|].
  rewrite !Cost.value_bind; fold (rank_of E u2 rx) (rank_of E u2 ry).
  destruct (Nat.compare (rank_of E u2 rx) (rank_of E u2 ry)); reflexivity.
Qed.

(** The boolean value compares representatives after two sequential finds. *)
Theorem equivb_equation {K} (E : encoding K) x y uf :
  equivb E x y uf =
  let '(rx, uf1) := find E x uf in
  let '(ry, uf2) := find E y uf1 in
  (eqb E rx ry, uf2).
Proof.
  unfold equivb, equivb_c; rewrite Cost.value_bind; fold (find E x uf).
  destruct (find E x uf) as [rx u1].
  rewrite Cost.value_bind; fold (find E y u1).
  destruct (find E y u1); reflexivity.
Qed.

Local Lemma known_equation {K} (uf : t K) :
  known uf = Map.combine (fun p r =>
    match p, r with
    | None, None => None
    | _, _ => Some tt
    end) (parents uf) (ranks uf).
Proof.
  reflexivity.
Qed.

Local Lemma firsts_value {K V} (xs : list (K * V)) :
  Cost.value (firsts_c xs) = List.map fst xs.
Proof.
  induction xs as [|[k v] rest IH]; [reflexivity|].
  cbn [firsts_c]; autorewrite with galois_cost; cbn [List.map fst].
  now rewrite IH.
Qed.

(** Keys are the ordered key projection of the union of both stored domains. *)
Theorem keys_equation {K} (E : encoding K) uf :
  keys E uf = List.map fst (Map.elements (Map.combine (fun p r =>
    match p, r with
    | None, None => None
    | _, _ => Some tt
    end) (parents uf) (ranks uf))).
Proof.
  unfold keys, keys_c; rewrite !Cost.value_bind, firsts_value.
  fold (known uf); fold (Map.elements (known uf)).
  now rewrite known_equation.
Qed.

Local Lemma unions_from_value {K} (E : encoding K) xs uf :
  Cost.value (unions_from_c E xs uf) =
  fold_left (fun acc xy => union E (fst xy) (snd xy) acc) xs uf.
Proof.
  revert uf; induction xs as [|[x y] xs IH]; intro uf; [reflexivity|].
  cbn [unions_from_c fold_left fst snd]; autorewrite with galois_cost.
  apply IH.
Qed.

(** Pair-list construction is a left fold of public union from the empty forest. *)
Theorem of_unions_equation {K} (E : encoding K) xs :
  of_unions E xs = fold_left (fun uf xy => union E (fst xy) (snd xy) uf) xs make.
Proof.
  unfold of_unions, of_unions_c; rewrite Cost.value_bind, unions_from_value; reflexivity.
Qed.

(** * Forest paths and compression *)

(** A path follows parent links and ends at a key without a parent. *)
Inductive reaches {K} (E : encoding K) (uf : t K) : K -> K -> Prop :=
  | Root x : Map.get E x (parents uf) = None -> reaches E uf x x
  | Step x y root : Map.get E x (parents uf) = Some y ->
      reaches E uf y root -> reaches E uf x root.

Local Lemma reaches_unique {K} (E : encoding K) uf x a b :
  reaches E uf x a -> reaches E uf x b -> a = b.
Proof.
  intro Hpath; revert b; induction Hpath as [x Hroot|x y a Hparent Hpath IH];
    intros b Hother; inversion Hother as [x' Hroot'|x' y' b' Hparent' Htail]; subst.
  - reflexivity.
  - congruence.
  - congruence.
  - assert (y = y') by congruence; subst y'; apply IH; exact Htail.
Qed.

Local Lemma reaches_root {K} (E : encoding K) uf x root :
  reaches E uf x root -> Map.get E root (parents uf) = None.
Proof.
  intro Hpath; induction Hpath; assumption.
Qed.

Local Lemma reaches_rank {K} (E : encoding K) uf x root :
  wf E uf -> reaches E uf x root -> rank_of E uf x <= rank_of E uf root.
Proof.
  intros [_ [_ [_ Hrank]]] Hpath; induction Hpath as [x Hroot|x y r Hparent Hpath IH].
  - lia.
  - specialize (Hrank x y Hparent); lia.
Qed.

Section Laws.
Context {K : Type} (E : encoding K) (HE : encoding_laws E).

Local Lemma redirect_wf uf x root :
  wf E uf -> rank_of E uf x < rank_of E uf root -> wf E (redirect E x root uf).
Proof.
  intros [Hp [Hr [Hbound Hstep]]] Hlt.
  rewrite redirect_equation; split.
  - apply Map.wf_set; exact Hp.
  - split; [exact Hr|]; split; [exact Hbound|]; intros a b Hget.
    cbn [parents] in Hget.
    destruct (eqb_dec E HE a x) as [Heq|Hne].
    + subst a; rewrite Map.get_set_same in Hget by exact Hp.
      inversion Hget; subst b; exact Hlt.
    + rewrite (Map.get_set_other E HE) in Hget by assumption; apply Hstep; exact Hget.
Qed.

Local Lemma redirect_root uf x root :
  Map.wf E (parents uf) -> x <> root -> Map.get E root (parents uf) = None ->
  Map.get E root (parents (redirect E x root uf)) = None.
Proof.
  intros Hp Hne Hroot; rewrite redirect_equation; cbn [parents].
  rewrite (Map.get_set_other E HE) by congruence; exact Hroot.
Qed.

Local Lemma redirect_reaches uf x root :
  Map.wf E (parents uf) -> x <> root -> reaches E uf x root ->
  forall a b, reaches E (redirect E x root uf) a b <-> reaches E uf a b.
Proof.
  intros Hp Hne Hpath a b; pose proof (reaches_root E uf x root Hpath) as Hroot; split.
  - intro Hnew; induction Hnew as [a Hnone|a y b Hparent Htail IH].
    + destruct (eqb_dec E HE a x) as [Heq|Hax].
      * subst a; rewrite redirect_equation in Hnone; cbn [parents] in Hnone.
        rewrite Map.get_set_same in Hnone by exact Hp; discriminate.
      * apply Root; rewrite redirect_equation in Hnone; cbn [parents] in Hnone.
        rewrite (Map.get_set_other E HE) in Hnone by assumption; exact Hnone.
    + rewrite redirect_equation in Hparent; cbn [parents] in Hparent.
      destruct (eqb_dec E HE a x) as [Heq|Hax].
      * subst a; rewrite Map.get_set_same in Hparent by exact Hp.
        inversion Hparent; subst y.
        assert (root = b) by
          (apply (reaches_unique E uf root root b); [apply Root|]; assumption).
        subst b; exact Hpath.
      * apply (Step E uf a y b);
          [rewrite (Map.get_set_other E HE) in Hparent by assumption|]; assumption.
  - intro Hold; induction Hold as [a Hnone|a y b Hparent Htail IH].
    + apply Root; rewrite redirect_equation; cbn [parents].
      destruct (eqb_dec E HE a x) as [Heq|Hax].
      * subst a; assert (x = root) by
          (apply (reaches_unique E uf x x root); [apply Root|]; assumption); contradiction.
      * rewrite (Map.get_set_other E HE) by assumption; exact Hnone.
    + destruct (eqb_dec E HE a x) as [Heq|Hax].
      * subst a.
        assert (b = root) by (eapply reaches_unique; [eapply Step; eassumption|exact Hpath]).
        subst b; apply (Step E (redirect E x root uf) x root root).
        -- rewrite redirect_equation; cbn [parents]; apply Map.get_set_same; exact Hp.
        -- apply Root; apply redirect_root; assumption.
      * apply (Step E (redirect E x root uf) a y b).
        -- rewrite redirect_equation; cbn [parents].
           rewrite (Map.get_set_other E HE) by assumption; exact Hparent.
        -- exact IH.
Qed.

Local Lemma find_fuel_ranks fuel x uf :
  ranks (snd (find_fuel E fuel x uf)) = ranks uf /\
  max_rank (snd (find_fuel E fuel x uf)) = max_rank uf.
Proof.
  revert x uf; induction fuel as [|fuel IH]; intros x uf; rewrite find_fuel_equation; [auto|].
  destruct (Map.get E x (parents uf)) as [y|]; [|auto].
  specialize (IH y uf); destruct (find_fuel E fuel y uf) as [root uf'].
  rewrite redirect_equation; exact IH.
Qed.

Local Lemma find_fuel_correct fuel : forall x uf,
  wf E uf -> max_rank uf < fuel + rank_of E uf x ->
  let '(root, uf') := find_fuel E fuel x uf in
  wf E uf' /\ reaches E uf x root /\
  (forall a b, reaches E uf' a b <-> reaches E uf a b).
Proof.
  induction fuel as [|fuel IH]; intros x uf Hwf Hfuel.
  - pose proof (proj1 (proj2 (proj2 Hwf)) x) as Hbound.
    change (max_rank uf < rank_of E uf x) in Hfuel; lia.
  - rewrite find_fuel_equation; destruct (Map.get E x (parents uf)) as [y|] eqn:Hparent.
    + pose proof (proj2 (proj2 (proj2 Hwf)) x y Hparent) as Hlt.
      specialize (IH y uf Hwf ltac:(lia)).
      pose proof (find_fuel_ranks fuel y uf) as Hranks.
      destruct (find_fuel E fuel y uf) as [root uf'] eqn:Hfind.
      destruct IH as [Hwf' [Hpath Hagree]]; cbn in Hranks.
      destruct Hranks as [Hranks Hmax].
      assert (Hxr : rank_of E uf' x < rank_of E uf' root).
      { rewrite !rank_of_equation, Hranks.
        rewrite <- (rank_of_equation E uf x), <- (rank_of_equation E uf root).
        pose proof (reaches_rank E uf y root Hwf Hpath); lia. }
      assert (Hne : x <> root) by (intro Heq; subst x; lia).
      assert (Hpathx : reaches E uf x root) by (eapply Step; eassumption).
      split; [apply redirect_wf; assumption|]; split; [exact Hpathx|].
      intros a b; rewrite (redirect_reaches uf' x root (proj1 Hwf') Hne
        (proj2 (Hagree x root) Hpathx)).
      apply Hagree.
    + split; [exact Hwf|]; split; [apply Root; exact Hparent|].
      intros a b; reflexivity.
Qed.

(** Find reaches an original root and keeps all paths and both stored Map invariants. *)
Theorem find_correct x uf : wf E uf ->
  wf E (snd (find E x uf)) /\ reaches E uf x (fst (find E x uf)) /\
  (forall a b, reaches E (snd (find E x uf)) a b <-> reaches E uf a b).
Proof.
  intro Hwf; pose proof (find_fuel_correct (S (max_rank uf)) x uf Hwf ltac:(lia)) as H.
  rewrite find_equation; destruct (find_fuel E (S (max_rank uf)) x uf); exact H.
Qed.

(** Path compression preserves well-formedness. *)
Theorem wf_find uf x : wf E uf -> wf E (snd (find E x uf)).
Proof.
  intro Hwf; exact (proj1 (find_correct x uf Hwf)).
Qed.

(** Finding one key preserves every representative. *)
Theorem find_rep_stable uf x y : wf E uf ->
  fst (find E x (snd (find E y uf))) = fst (find E x uf).
Proof.
  intro Hwf; destruct (find_correct y uf Hwf) as [Hwf' [_ Hagree]].
  apply (reaches_unique E uf x).
  - apply Hagree; exact (proj1 (proj2 (find_correct x _ Hwf'))).
  - exact (proj1 (proj2 (find_correct x uf Hwf))).
Qed.

(** A representative is a root and represents itself. *)
Theorem find_rep_canonical uf x : wf E uf ->
  fst (find E (fst (find E x uf)) uf) = fst (find E x uf).
Proof.
  intro Hwf; apply (reaches_unique E uf (fst (find E x uf))).
  - exact (proj1 (proj2 (find_correct _ uf Hwf))).
  - apply Root; eapply reaches_root; exact (proj1 (proj2 (find_correct x uf Hwf))).
Qed.

(** Find returns a key without a parent in both the original and compressed forest. *)
Theorem find_root uf x : wf E uf ->
  Map.get E (fst (find E x uf)) (parents uf) = None /\
  Map.get E (fst (find E x uf)) (parents (snd (find E x uf))) = None.
Proof.
  intro Hwf; destruct (find_correct x uf Hwf) as [Hnew [Hpath Hagree]].
  split; eapply reaches_root; [exact Hpath|apply Hagree; exact Hpath].
Qed.

(** Find relates the input to its representative and compression keeps every equivalence class. *)
Theorem find_equiv uf x : wf E uf ->
  equiv E uf x (fst (find E x uf)) /\
  (forall a b, equiv E (snd (find E x uf)) a b <-> equiv E uf a b).
Proof.
  intro Hwf; split.
  - unfold equiv; symmetry; apply find_rep_canonical; exact Hwf.
  - intros a b; unfold equiv; rewrite !find_rep_stable by exact Hwf; reflexivity.
Qed.

End Laws.

(** Equality of representatives is an equivalence even for malformed forests. *)
Theorem equiv_refl_sym_trans {K} (E : encoding K) (uf : t K) :
  equivalence K (equiv E uf).
Proof.
  constructor; unfold reflexive, symmetric, transitive, equiv; congruence.
Qed.

(** The initial forest satisfies the rank and stored Map invariants without encoding laws. *)
Theorem wf_make {K} (E : encoding K) : wf E (@make K).
Proof.
  rewrite make_equation; split; [apply Map.wf_empty|].
  split; [apply Map.wf_empty|]; split.
  - intro x; rewrite rank_of_equation; cbn [ranks max_rank]; rewrite Map.get_empty; lia.
  - intros x y Hget; cbn [parents] in Hget; rewrite Map.get_empty in Hget; discriminate.
Qed.

(** Initially equal keys, including unknown keys, are precisely the equivalent pairs. *)
Theorem make_equiv {K} (E : encoding K) a b : equiv E make a b <-> a = b.
Proof.
  unfold equiv; rewrite !find_equation, make_equation; cbn [max_rank].
  rewrite !find_fuel_equation; cbn [parents]; rewrite !Map.get_empty; reflexivity.
Qed.

(** A supported key has a stored parent or a stored rank. *)
Definition support {K} (E : encoding K) (uf : t K) x : Prop :=
  Map.get E x (parents uf) <> None \/ Map.get E x (ranks uf) <> None.

Section SupportAndUnion.
Context {K : Type} (E : encoding K) (HE : encoding_laws E).

Local Lemma known_wf uf : wf E uf -> Map.wf E (known uf).
Proof.
  intros [Hp [Hr _]]; rewrite known_equation.
  apply Map.wf_combine; assumption.
Qed.

(** Enumeration contains precisely keys stored in either Map under the forest invariant. *)
Theorem keys_spec uf x : wf E uf -> (In x (keys E uf) <-> support E uf x).
Proof.
  intro Hwf; rewrite keys_equation, <- known_equation.
  assert (Hin : In x (List.map fst (Map.elements (known uf))) <->
    Map.get E x (known uf) = Some tt).
  { rewrite in_map_iff; split.
    - intros [[k []] [Heq Hin]]; cbn in Heq; subst k.
      apply (Map.elements_spec E HE); [apply known_wf; exact Hwf|exact Hin].
    - intro Hget; exists (x, tt); split; [reflexivity|].
      apply (Map.elements_spec E HE); [apply known_wf; exact Hwf|exact Hget]. }
  rewrite Hin, known_equation, Map.get_combine
    by (try reflexivity; exact (proj1 Hwf) || exact (proj1 (proj2 Hwf))).
  unfold support.
  destruct (Map.get E x (parents uf)), (Map.get E x (ranks uf));
    cbn; intuition discriminate.
Qed.

Local Lemma sorted_keys_nodup (xs : list (K * unit)) :
  StronglySorted (fun a b => Map.code_compare (encode E (fst a)) (encode E (fst b)) = Lt)
    xs -> NoDup (List.map fst xs).
Proof.
  intro Hsort; induction Hsort as [|a xs Hsort IH Hafter]; cbn [List.map].
  - constructor.
  - constructor; [|exact IH].
    rewrite in_map_iff; intros [b [Heq Hin]].
    rewrite Forall_forall in Hafter; specialize (Hafter b Hin).
    rewrite Heq in Hafter.
    pose proof (proj2 (Map.code_compare_eq (encode E (fst a)) (encode E (fst a))) eq_refl).
    congruence.
Qed.

(** Enumerating support never repeats a key. *)
Theorem keys_nodup uf : wf E uf -> NoDup (keys E uf).
Proof.
  intro Hwf; rewrite keys_equation, <- known_equation.
  apply sorted_keys_nodup; apply Map.elements_sorted; apply known_wf; exact Hwf.
Qed.

Local Lemma find_fuel_maps fuel x uf :
  Map.wf E (parents uf) -> Map.wf E (parents (snd (find_fuel E fuel x uf))).
Proof.
  revert x uf; induction fuel as [|fuel IH]; intros x uf Hp.
  - rewrite find_fuel_equation; exact Hp.
  - rewrite find_fuel_equation.
    destruct (Map.get E x (parents uf)) as [y|]; [|exact Hp].
    specialize (IH y uf Hp); destruct (find_fuel E fuel y uf) as [root uf'].
    rewrite redirect_equation; cbn [parents snd]; apply Map.wf_set; exact IH.
Qed.

Local Lemma find_fuel_domain fuel : forall x uf a,
  Map.wf E (parents uf) ->
  (Map.get E a (parents (snd (find_fuel E fuel x uf))) = None <->
   Map.get E a (parents uf) = None).
Proof.
  induction fuel as [|fuel IH]; intros x uf a Hp; rewrite find_fuel_equation;
    [reflexivity|].
  destruct (Map.get E x (parents uf)) as [y|] eqn:Hparent; [|reflexivity].
  specialize (IH y uf a Hp).
  pose proof (find_fuel_maps fuel y uf Hp) as Hp'.
  destruct (find_fuel E fuel y uf) as [root uf']; cbn [snd] in IH, Hp'.
  rewrite redirect_equation; cbn [parents snd].
  destruct (eqb_dec E HE a x) as [Heq|Hne].
  - subst a; rewrite Map.get_set_same by exact Hp'; rewrite Hparent; split; discriminate.
  - rewrite (Map.get_set_other E HE) by assumption; exact IH.
Qed.

(** Find neither registers nor removes keys from support. *)
Theorem find_support x uf a : wf E uf ->
  (support E (snd (find E x uf)) a <-> support E uf a).
Proof.
  intro Hwf; unfold support; rewrite find_equation.
  destruct (find_fuel_ranks E (S (max_rank uf)) x uf) as [Hr Hmax].
  rewrite Hr; pose proof (find_fuel_domain (S (max_rank uf)) x uf a (proj1 Hwf)); tauto.
Qed.

Local Lemma reaches_strict uf x root :
  wf E uf -> reaches E uf x root -> x <> root -> rank_of E uf x < rank_of E uf root.
Proof.
  intros Hwf Hpath Hne; inversion Hpath as [a Hnone|a y r Hparent Htail]; subst.
  - contradiction.
  - pose proof (proj2 (proj2 (proj2 Hwf)) x y Hparent).
    pose proof (reaches_rank E uf y root Hwf Htail); lia.
Qed.

Local Lemma positive_rank_support uf x : 0 < rank_of E uf x -> support E uf x.
Proof.
  rewrite rank_of_equation; unfold support; destruct (Map.get E x (ranks uf)) eqn:Hrank.
  - intro Hpositive; right; discriminate.
  - lia.
Qed.

Local Lemma path_support uf x root :
  wf E uf -> reaches E uf x root -> x = root \/ (support E uf x /\ support E uf root).
Proof.
  intros Hwf Hpath; destruct (eqb_dec E HE x root) as [Heq|Hne]; [auto|right].
  split.
  - inversion Hpath as [a Hnone|a y r Hparent Htail]; subst; [contradiction|].
    left; rewrite Hparent; discriminate.
  - apply positive_rank_support; pose proof (reaches_strict uf x root Hwf Hpath Hne); lia.
Qed.

(** A key outside support is alone in its class, including every unknown key. *)
Theorem keys_support uf x y : wf E uf -> ~ In x (keys E uf) ->
  equiv E uf x y -> y = x.
Proof.
  intros Hwf Houtside Hequiv; rewrite (keys_spec uf x Hwf) in Houtside.
  destruct (Map.get E x (parents uf)) as [parent|] eqn:Hparent.
  - exfalso; apply Houtside; left; rewrite Hparent; discriminate.
  - assert (Hrep : fst (find E x uf) = x).
    { apply (reaches_unique E uf x);
        [exact (proj1 (proj2 (find_correct E HE x uf Hwf)))|].
      apply Root; exact Hparent. }
    unfold equiv in Hequiv; rewrite Hrep in Hequiv.
    pose proof (proj1 (proj2 (find_correct E HE y uf Hwf))) as Hpath.
    rewrite <- Hequiv in Hpath; destruct (path_support uf y x Hwf Hpath)
      as [Heq|[_ Hsupport]].
    + exact Heq.
    + contradiction.
Qed.

Local Lemma touch_ranks x uf a : Map.wf E (ranks uf) ->
  rank_of E (touch E x uf) a = rank_of E uf a.
Proof.
  intro Hr; rewrite touch_equation; destruct (Map.get E x (ranks uf)) eqn:Hrank;
    [reflexivity|].
  rewrite !rank_of_equation; cbn [ranks].
  destruct (eqb_dec E HE a x) as [Heq|Hne].
  - subst a; rewrite Map.get_set_same by exact Hr; rewrite Hrank; reflexivity.
  - rewrite (Map.get_set_other E HE) by assumption; reflexivity.
Qed.

Local Lemma touch_parents x uf : parents (touch E x uf) = parents uf.
Proof.
  rewrite touch_equation; destruct (Map.get E x (ranks uf)); reflexivity.
Qed.

Local Lemma touch_wf x uf : wf E uf -> wf E (touch E x uf).
Proof.
  intros [Hp [Hr [Hb Hs]]]; split; [rewrite touch_parents; exact Hp|].
  split.
  - rewrite touch_equation; destruct (Map.get E x (ranks uf));
      [exact Hr|apply Map.wf_set; exact Hr].
  - split.
    + intro a; rewrite touch_ranks by exact Hr.
      rewrite touch_equation; destruct (Map.get E x (ranks uf)); apply Hb.
    + intros a b Hget; rewrite touch_parents in Hget.
      rewrite !touch_ranks by exact Hr; apply Hs; exact Hget.
Qed.

Local Lemma touch_reaches x uf a b :
  reaches E (touch E x uf) a b <-> reaches E uf a b.
Proof.
  split; intro H; induction H; [apply Root|eapply Step|apply Root|eapply Step];
    try rewrite touch_parents in *; eassumption.
Qed.

Local Lemma touch_support x uf a : Map.wf E (ranks uf) ->
  (support E (touch E x uf) a <-> a = x \/ support E uf a).
Proof.
  intro Hr; unfold support; rewrite touch_parents, touch_equation.
  destruct (Map.get E x (ranks uf)) eqn:Hrank.
  - destruct (eqb_dec E HE a x) as [Heq|Hne];
      [subst a; rewrite Hrank|]; intuition discriminate.
  - cbn [ranks]; destruct (eqb_dec E HE a x) as [Heq|Hne].
    + subst a; rewrite Map.get_set_same by exact Hr; intuition discriminate.
    + rewrite (Map.get_set_other E HE) by assumption; tauto.
Qed.

Local Lemma touch_rep x uf a : wf E uf ->
  fst (find E a (touch E x uf)) = fst (find E a uf).
Proof.
  intro Hwf; apply (reaches_unique E uf a).
  - apply (proj1 (touch_reaches x uf a _)).
    exact (proj1 (proj2 (find_correct E HE a _ (touch_wf x uf Hwf)))).
  - exact (proj1 (proj2 (find_correct E HE a uf Hwf))).
Qed.

Local Lemma link_parents child root raise uf :
  parents (link E child root raise uf) = Map.set E child root (parents uf).
Proof.
  rewrite link_equation; destruct raise; [reflexivity|].
  rewrite redirect_equation; reflexivity.
Qed.

Local Lemma link_rank_root child root uf : Map.wf E (ranks uf) ->
  rank_of E (link E child root true uf) root = S (rank_of E uf root).
Proof.
  intro Hr; rewrite link_equation, rank_of_equation; cbn [ranks].
  rewrite Map.get_set_same by exact Hr; reflexivity.
Qed.

Local Lemma link_rank_other child root uf a : Map.wf E (ranks uf) -> a <> root ->
  rank_of E (link E child root true uf) a = rank_of E uf a.
Proof.
  intros Hr Hne; rewrite link_equation, !rank_of_equation; cbn [ranks].
  rewrite (Map.get_set_other E HE) by assumption; reflexivity.
Qed.

Local Lemma link_raise_wf child root uf :
  wf E uf -> child <> root -> Map.get E root (parents uf) = None ->
  rank_of E uf child <= rank_of E uf root -> wf E (link E child root true uf).
Proof.
  intros [Hp [Hr [Hbound Hstep]]] Hne Hroot Hrank; split.
  - rewrite link_parents; apply Map.wf_set; exact Hp.
  - split.
    + rewrite link_equation; cbn [ranks]; apply Map.wf_set; exact Hr.
    + split.
      * intro a; destruct (eqb_dec E HE a root) as [Heq|Har].
        -- subst a; rewrite link_rank_root by exact Hr.
           rewrite link_equation; cbn [max_rank]; apply Nat.le_max_r.
        -- rewrite link_rank_other by assumption; rewrite link_equation; cbn [max_rank].
           eapply Nat.le_trans; [apply Hbound|apply Nat.le_max_l].
      * intros a b Hget; rewrite link_parents in Hget.
        destruct (eqb_dec E HE a child) as [Heq|Hac].
        -- subst a; rewrite Map.get_set_same in Hget by exact Hp.
           inversion Hget; subst b; rewrite link_rank_root, link_rank_other by assumption; lia.
        -- rewrite (Map.get_set_other E HE) in Hget by assumption.
           assert (Har : a <> root) by (intro Heq; subst a; congruence).
           rewrite link_rank_other by assumption; specialize (Hstep a b Hget).
           destruct (eqb_dec E HE b root) as [Heq|Hbr].
           ++ subst b; rewrite link_rank_root by exact Hr; lia.
           ++ rewrite link_rank_other by assumption; exact Hstep.
Qed.

Local Lemma link_path child root raise uf :
  Map.wf E (parents uf) -> child <> root -> Map.get E child (parents uf) = None ->
  Map.get E root (parents uf) = None -> forall a b,
  reaches E uf a b -> reaches E (link E child root raise uf) a
    (if eqb E b child then root else b).
Proof.
  intros Hp Hne Hchild Hroot a b Hpath;
    induction Hpath as [a Hnone|a y b Hparent Htail IH].
  - destruct (eqb E a child) eqn:Heq.
    + apply (eqb_true_iff E HE) in Heq; subst a.
      apply (Step E _ child root root).
      * rewrite link_parents; apply Map.get_set_same; exact Hp.
      * apply Root; rewrite link_parents, (Map.get_set_other E HE) by congruence; exact Hroot.
    + apply Root; rewrite link_parents, (Map.get_set_other E HE).
      * exact Hnone.
      * exact Hp.
      * intro Hequal; subst a; rewrite eqb_refl in Heq; discriminate.
  - apply (Step E _ a y _); [|exact IH].
    rewrite link_parents, (Map.get_set_other E HE); [exact Hparent|exact Hp|].
    intro Heq; subst a; congruence.
Qed.

Local Lemma link_rep child root raise uf a :
  wf E uf -> wf E (link E child root raise uf) -> child <> root ->
  Map.get E child (parents uf) = None -> Map.get E root (parents uf) = None ->
  fst (find E a (link E child root raise uf)) =
    if eqb E (fst (find E a uf)) child then root else fst (find E a uf).
Proof.
  intros Hwf Hnew Hne Hchild Hroot.
  apply (reaches_unique E (link E child root raise uf) a).
  - exact (proj1 (proj2 (find_correct E HE a _ Hnew))).
  - apply link_path; try assumption; [exact (proj1 Hwf)|].
    exact (proj1 (proj2 (find_correct E HE a uf Hwf))).
Qed.

Local Lemma find_state x uf root uf' :
  wf E uf -> find E x uf = (root, uf') ->
  wf E uf' /\ Map.get E root (parents uf') = None /\
  root = fst (find E x uf) /\
  (forall a, fst (find E a uf') = fst (find E a uf)) /\
  (forall a, support E uf' a <-> support E uf a).
Proof.
  intros Hwf Hfind; pose proof (find_correct E HE x uf Hwf) as Hcorrect.
  rewrite Hfind in Hcorrect; cbn [fst snd] in Hcorrect.
  destruct Hcorrect as [Hwf' [Hpath Hagree]].
  split; [exact Hwf'|]; split.
  - eapply reaches_root; apply Hagree; exact Hpath.
  - split; [rewrite Hfind; reflexivity|]; split.
    + intro a; pose proof (find_rep_stable E HE uf a x Hwf) as Hstable.
      rewrite Hfind in Hstable; exact Hstable.
    + intro a; pose proof (find_support x uf a Hwf) as Hsupport.
      rewrite Hfind in Hsupport; exact Hsupport.
Qed.

Local Lemma two_finds uf x y rx u1 ry u2 :
  wf E uf -> find E x uf = (rx, u1) -> find E y u1 = (ry, u2) ->
  wf E u2 /\ Map.get E rx (parents u2) = None /\ Map.get E ry (parents u2) = None /\
  rx = fst (find E x uf) /\ ry = fst (find E y uf) /\
  (forall a, fst (find E a u2) = fst (find E a uf)) /\
  (forall a, support E u2 a <-> support E uf a).
Proof.
  intros Hwf Hx Hy.
  destruct (find_state x uf rx u1 Hwf Hx) as [Hw1 [Hrx [Hrxrep [Hstable1 Hsupport1]]]].
  destruct (find_state y u1 ry u2 Hw1 Hy) as [Hw2 [Hry [Hryrep [Hstable2 Hsupport2]]]].
  split; [exact Hw2|]; split.
  - pose proof (proj2 (proj2 (find_correct E HE y u1 Hw1)) rx rx) as Hagree.
    rewrite Hy in Hagree; cbn [snd] in Hagree.
    apply (reaches_root E u2 rx rx); apply Hagree; apply Root; exact Hrx.
  - split; [exact Hry|]; split; [exact Hrxrep|]; split.
    + rewrite Hryrep; apply Hstable1.
    + split.
      * intro a; rewrite Hstable2, Hstable1; reflexivity.
      * intro a; rewrite Hsupport2, Hsupport1; reflexivity.
Qed.

(** Union by rank preserves both Map invariants and the forest rank invariant. *)
Theorem wf_union uf x y : wf E uf -> wf E (union E x y uf).
Proof.
  intro Hwf; rewrite union_equation.
  destruct (find E x uf) as [rx u1] eqn:Hx.
  destruct (find E y u1) as [ry u2] eqn:Hy.
  destruct (two_finds uf x y rx u1 ry u2 Hwf Hx Hy)
    as [Hw2 [Hrx [Hry [Hrxrep [Hryrep [Hstable Hsupport]]]]]].
  destruct (eqb E rx ry) eqn:Heq.
  - apply touch_wf; exact Hw2.
  - apply (eqb_false_iff E HE) in Heq.
    destruct (Nat.compare (rank_of E u2 rx) (rank_of E u2 ry)) eqn:Hcmp.
    + apply Nat.compare_eq_iff in Hcmp.
      apply link_raise_wf; [exact Hw2|congruence|exact Hrx|lia].
    + apply Nat.compare_lt_iff in Hcmp; rewrite link_equation.
      apply (redirect_wf E HE); assumption.
    + apply Nat.compare_gt_iff in Hcmp; rewrite link_equation.
      apply (redirect_wf E HE); assumption.
Qed.

(** The boolean test reflects equivalence and keeps the invariant and all classes. *)
Theorem equivb_correct uf x y : wf E uf ->
  (fst (equivb E x y uf) = true <-> equiv E uf x y) /\
  wf E (snd (equivb E x y uf)) /\
  (forall a b, equiv E (snd (equivb E x y uf)) a b <-> equiv E uf a b).
Proof.
  intro Hwf; rewrite equivb_equation.
  destruct (find E x uf) as [rx u1] eqn:Hx.
  destruct (find E y u1) as [ry u2] eqn:Hy.
  destruct (two_finds uf x y rx u1 ry u2 Hwf Hx Hy)
    as [Hw2 [Hrx [Hry [Hrxrep [Hryrep [Hstable Hsupport]]]]]].
  cbn [fst snd]; split.
  - rewrite (eqb_true_iff E HE), Hrxrep, Hryrep; reflexivity.
  - split; [exact Hw2|]; intros a b; unfold equiv; rewrite !Hstable; reflexivity.
Qed.

(** Collapsing one root identifies exactly that pair of representatives. *)
Local Definition collapse (child root a : K) : K :=
  if eqb E a child then root else a.

Local Lemma collapse_equal child root a b : child <> root ->
  (collapse child root a = collapse child root b <->
    a = b \/ (a = child /\ root = b) \/ (a = root /\ child = b)).
Proof.
  intro Hne; unfold collapse.
  destruct (eqb_spec E HE a child) as [Ha|Ha];
    destruct (eqb_spec E HE b child) as [Hb|Hb];
    intuition congruence.
Qed.

Local Lemma link_equiv child root raise uf a b :
  wf E uf -> wf E (link E child root raise uf) -> child <> root ->
  Map.get E child (parents uf) = None -> Map.get E root (parents uf) = None ->
  (equiv E (link E child root raise uf) a b <-> equiv E uf a b \/
    (fst (find E a uf) = child /\ root = fst (find E b uf)) \/
    (fst (find E a uf) = root /\ child = fst (find E b uf))).
Proof.
  intros Hwf Hnew Hne Hchild Hroot; unfold equiv.
  rewrite !link_rep by assumption; apply collapse_equal; exact Hne.
Qed.

(** Union merges precisely its two argument classes and keeps every other class separate. *)
Theorem union_equiv uf x y a b : wf E uf ->
  (equiv E (union E x y uf) a b <-> equiv E uf a b \/
    (equiv E uf a x /\ equiv E uf y b) \/ (equiv E uf a y /\ equiv E uf x b)).
Proof.
  intro Hwf; pose proof (wf_union uf x y Hwf) as Hnew.
  rewrite union_equation in *.
  destruct (find E x uf) as [rx u1] eqn:Hx.
  destruct (find E y u1) as [ry u2] eqn:Hy.
  destruct (two_finds uf x y rx u1 ry u2 Hwf Hx Hy)
    as [Hw2 [Hrx [Hry [Hrxrep [Hryrep [Hstable Hsupport]]]]]].
  destruct (eqb E rx ry) eqn:Heq.
  - apply (eqb_true_iff E HE) in Heq; unfold equiv.
    rewrite !touch_rep by exact Hw2; rewrite !Hstable.
    rewrite <- Hrxrep, <- Hryrep; subst ry; intuition congruence.
  - apply (eqb_false_iff E HE) in Heq.
    destruct (Nat.compare (rank_of E u2 rx) (rank_of E u2 ry)) eqn:Hcmp.
    + rewrite (link_equiv ry rx true u2 a b) by (try assumption; congruence).
      unfold equiv; rewrite !Hstable, <- Hrxrep, <- Hryrep; tauto.
    + rewrite (link_equiv rx ry false u2 a b) by assumption.
      unfold equiv; rewrite !Hstable, <- Hrxrep, <- Hryrep; tauto.
    + rewrite (link_equiv ry rx false u2 a b) by (try assumption; congruence).
      unfold equiv; rewrite !Hstable, <- Hrxrep, <- Hryrep; tauto.
Qed.

Local Lemma link_support child root raise uf z : wf E uf ->
  (support E (link E child root raise uf) z <->
    z = child \/ (raise = true /\ z = root) \/ support E uf z).
Proof.
  intros [Hp [Hr _]]; unfold support; rewrite link_parents.
  rewrite link_equation; destruct raise; cbn [ranks].
  - destruct (eqb_dec E HE z child) as [Heq|Hne].
    + subst z; rewrite Map.get_set_same by exact Hp; intuition discriminate.
    + rewrite (Map.get_set_other E HE) by assumption.
      destruct (eqb_dec E HE z root) as [Heq|Hnr].
      * subst z; rewrite Map.get_set_same by exact Hr; intuition discriminate.
      * rewrite (Map.get_set_other E HE) by assumption; intuition discriminate.
  - rewrite redirect_equation; cbn [ranks].
    destruct (eqb_dec E HE z child) as [Heq|Hne].
    + subst z; rewrite Map.get_set_same by exact Hp; intuition discriminate.
    + rewrite (Map.get_set_other E HE) by assumption; intuition discriminate.
Qed.

Local Lemma roots_support uf x y rx ry z :
  wf E uf -> reaches E uf x rx -> reaches E uf y ry ->
  (z = rx \/ z = ry \/ support E uf z <-> z = x \/ z = y \/ support E uf z).
Proof.
  intros Hwf Hx Hy.
  destruct (path_support uf x rx Hwf Hx) as [Hxroot|[Hsx Hsrx]];
    destruct (path_support uf y ry Hwf Hy) as [Hyroot|[Hsy Hsry]];
    intuition congruence.
Qed.

Local Lemma union_support uf x y z : wf E uf ->
  (support E (union E x y uf) z <-> z = x \/ z = y \/ support E uf z).
Proof.
  intro Hwf; rewrite union_equation.
  destruct (find E x uf) as [rx u1] eqn:Hx.
  destruct (find E y u1) as [ry u2] eqn:Hy.
  destruct (two_finds uf x y rx u1 ry u2 Hwf Hx Hy)
    as [Hw2 [Hrx [Hry [Hrxrep [Hryrep [Hstable Hsupport]]]]]].
  assert (Hpaths : reaches E uf x rx /\ reaches E uf y ry).
  { rewrite Hrxrep, Hryrep; split; apply (proj1 (proj2 (find_correct E HE _ uf Hwf))). }
  destruct Hpaths as [Hpathx Hpathy].
  rewrite <- (roots_support uf x y rx ry z Hwf Hpathx Hpathy), <- (Hsupport z).
  destruct (eqb E rx ry) eqn:Heq.
  - apply (eqb_true_iff E HE) in Heq.
    rewrite touch_support by exact (proj1 (proj2 Hw2)); rewrite <- Heq; tauto.
  - destruct (Nat.compare (rank_of E u2 rx) (rank_of E u2 ry)) eqn:Hcmp;
      rewrite link_support by exact Hw2.
    + intuition.
    + apply Nat.compare_lt_iff in Hcmp.
      assert (Hsry : support E u2 ry) by (apply positive_rank_support; lia).
      intuition congruence.
    + apply Nat.compare_gt_iff in Hcmp.
      assert (Hsrx : support E u2 rx) by (apply positive_rank_support; lia).
      intuition congruence.
Qed.

(** Union records precisely its two arguments in addition to existing support. *)
Theorem keys_union uf x y z : wf E uf ->
  (In z (keys E (union E x y uf)) <-> z = x \/ z = y \/ In z (keys E uf)).
Proof.
  intro Hwf; rewrite !keys_spec by (try exact Hwf; apply wf_union; exact Hwf).
  apply union_support; exact Hwf.
Qed.

End SupportAndUnion.

(** The initial support is empty. *)
Theorem keys_make {K} (E : encoding K) : keys E (@make K) = nil.
Proof.
  reflexivity.
Qed.

(** * Pair-list construction *)

Local Definition merged {K} (R : K -> K -> Prop) (x y a b : K) : Prop :=
  R a b \/ (R a x /\ R y b) \/ (R a y /\ R x b).

Local Lemma merged_equivalence {K} (R : K -> K -> Prop) x y :
  equivalence K R -> equivalence K (merged R x y).
Proof.
  intros [Hrefl Htrans Hsym]; constructor.
  - intro a; left; apply Hrefl.
  - intros a b c [Hab|[[Hax Hyb]|[Hay Hxb]]] [Hbc|[[Hbx Hyc]|[Hby Hxc]]];
      unfold merged; eauto 5.
  - intros a b [Hab|[[Hax Hyb]|[Hay Hxb]]].
    + left; apply Hsym; exact Hab.
    + right; right; split; apply Hsym; assumption.
    + right; left; split; apply Hsym; assumption.
Qed.

Local Lemma closure_equivalence {K} (R : K -> K -> Prop) :
  equivalence K (clos_refl_sym_trans K R).
Proof.
  constructor; [intro x; apply rst_refl|
    intros x y z Hxy Hyz; eapply rst_trans; eassumption|
    intros x y H; apply rst_sym; exact H].
Qed.

Local Lemma closure_mono {K} (R S : K -> K -> Prop) :
  (forall x y, R x y -> S x y) -> forall a b,
  clos_refl_sym_trans K R a b -> clos_refl_sym_trans K S a b.
Proof.
  intros Hincl a b Hpath; induction Hpath.
  - apply rst_step; apply Hincl; assumption.
  - apply rst_refl.
  - apply rst_sym; assumption.
  - eapply rst_trans; eassumption.
Qed.

Local Lemma closure_snoc {K} (l : list (K * K)) x y a b :
  clos_refl_sym_trans K (fun a b => In (a, b) (l ++ [(x, y)])) a b <->
  merged (clos_refl_sym_trans K (fun a b => In (a, b) l)) x y a b.
Proof.
  set (R := clos_refl_sym_trans K (fun a b => In (a, b) l)).
  assert (Hmerged : equivalence K (merged R x y)) by
    (apply merged_equivalence; apply closure_equivalence).
  destruct Hmerged as [Hrefl Htrans Hsym]; split.
  - intro Hpath; induction Hpath as [u v Hpair|u|u v Hpath IH|u v w Huv IHuv Hvw IHvw].
    + apply in_app_iff in Hpair; destruct Hpair as [Hold|Hnew].
      * left; apply rst_step; exact Hold.
      * cbn in Hnew; destruct Hnew as [Heq|Hfalse]; [inversion Heq; subst|contradiction].
        right; left; split; apply rst_refl.
    + apply Hrefl.
    + apply Hsym; exact IH.
    + eapply Htrans; eassumption.
  - assert (Hembed : forall u v, R u v ->
        clos_refl_sym_trans K (fun a b => In (a, b) (l ++ [(x, y)])) u v).
    { apply closure_mono; intros u v Hin; apply in_or_app; left; exact Hin. }
    assert (Hxy : clos_refl_sym_trans K (fun a b => In (a, b) (l ++ [(x, y)])) x y).
    { apply rst_step; apply in_or_app; right; cbn; auto. }
    intros [Hab|[[Hax Hyb]|[Hay Hxb]]].
    + apply Hembed; exact Hab.
    + eapply rst_trans; [apply Hembed; exact Hax|].
      eapply rst_trans; [exact Hxy|apply Hembed; exact Hyb].
    + eapply rst_trans; [apply Hembed; exact Hay|].
      eapply rst_trans; [apply rst_sym; exact Hxy|apply Hembed; exact Hxb].
Qed.

(** Building any pair list establishes both stored Map invariants and the rank invariant. *)
Theorem of_unions_wf {K} (E : encoding K) (HE : encoding_laws E) l :
  wf E (of_unions E l).
Proof.
  rewrite of_unions_equation; generalize (@make K) (wf_make E).
  induction l as [|[x y] l IH]; intros uf Hwf; cbn [fold_left fst snd]; [exact Hwf|].
  apply IH; apply (wf_union E HE); exact Hwf.
Qed.

(** The generated partition is the reflexive symmetric transitive closure of the input pairs. *)
Theorem of_unions_equiv {K} (E : encoding K) (HE : encoding_laws E) a b l :
  equiv E (of_unions E l) a b <->
  clos_refl_sym_trans K (fun x y => In (x, y) l) a b.
Proof.
  revert a b; induction l using rev_ind; intros a b.
  - rewrite of_unions_equation; cbn [fold_left]; rewrite make_equiv; split.
    + intro Heq; subst b; apply rst_refl.
    + intro Hpath; induction Hpath as [u v Hempty|u|u v Hpath IH|
        u v w Huv IHuv Hvw IHvw].
      * contradiction.
      * reflexivity.
      * symmetry; exact IH.
      * etransitivity; eassumption.
  - destruct x as [x y]; rewrite of_unions_equation at 1.
    rewrite fold_left_app; cbn [fold_left fst snd].
    rewrite <- of_unions_equation, (union_equiv E HE) by apply (of_unions_wf E HE).
    rewrite closure_snoc; unfold merged; rewrite !IHl; reflexivity.
Qed.

(** The legacy equivalence name denotes the same unconditional equivalence law. *)
Theorem equiv_equivalence {K} (E : encoding K) (uf : t K) :
  equivalence K (equiv E uf).
Proof.
  apply equiv_refl_sym_trans.
Qed.

(** * Callee-relative costs

    These equations account for the reference calls without assuming the later rank-size bounds.
    Encoding and key-comparison costs are retained by the costed Map and equality operations.
    Domain callbacks use one-tick pure lifts in addition to the Map callback overhead. *)

(** Rank lookup charges precisely its underlying Map lookup. *)
Theorem rank_of_cost {K} (E : encoding K) uf x :
  Cost.ticks (rank_of_c E uf x) = Cost.ticks (Map.get_c E x (ranks uf)).
Proof.
  unfold rank_of_c; apply Cost.ticks_map.
Qed.

(** A redirect charges precisely its underlying Map update. *)
Theorem redirect_cost {K} (E : encoding K) x root uf :
  Cost.ticks (redirect_c E x root uf) = Cost.ticks (Map.set_c E x root (parents uf)).
Proof.
  unfold redirect_c; rewrite Cost.ticks_bind, Cost.ticks_ret; lia.
Qed.

(** Each visited find frame charges one tick, its lookup, recursion and compression update. *)
Local Lemma reference_find_fuel_ticks {K} (E : encoding K) fuel x uf :
  Cost.ticks (find_fuel_c E fuel x uf) =
  match fuel with
  | 0 => 0%N
  | S rest =>
    (1 + Cost.ticks (Map.get_c E x (parents uf)) +
      match Map.get E x (parents uf) with
      | None => 0
      | Some y =>
        let '(root, compressed) := find_fuel E rest y uf in
        Cost.ticks (find_fuel_c E rest y uf) +
          Cost.ticks (Map.set_c E x root (parents compressed))
      end)%N
  end.
Proof.
  destruct fuel as [|fuel]; [reflexivity|].
  cbn [find_fuel_c]; autorewrite with galois_cost; fold (Map.get E x (parents uf)).
  destruct (Map.get E x (parents uf)) as [y|];
    [|rewrite Cost.ticks_ret; lia].
  rewrite Cost.ticks_bind; fold (find_fuel E fuel y uf).
  destruct (find_fuel E fuel y uf) as [root compressed].
  rewrite Cost.ticks_bind, Cost.ticks_ret, redirect_cost; lia.
Qed.

(** Public find's exact cost is its first frame plus the charged tail and redirect calls. *)
Local Lemma reference_find_ticks {K} (E : encoding K) x uf :
  Cost.ticks (find_c E x uf) =
  (1 + Cost.ticks (Map.get_c E x (parents uf)) +
    match Map.get E x (parents uf) with
    | None => 0
    | Some y =>
      let '(root, compressed) := find_fuel E (max_rank uf) y uf in
      Cost.ticks (find_fuel_c E (max_rank uf) y uf) +
        Cost.ticks (Map.set_c E x root (parents compressed))
    end)%N.
Proof.
  exact (reference_find_fuel_ticks E (S (max_rank uf)) x uf).
Qed.

(** Union charges its two finds, equality, optional rank queries and selected touch or link. *)
Local Lemma reference_union_ticks {K} (E : encoding K) x y uf :
  Cost.ticks (union_c E x y uf) =
  let '(rx, uf1) := find E x uf in
  let '(ry, uf2) := find E y uf1 in
  (Cost.ticks (find_c E x uf) + Cost.ticks (find_c E y uf1) +
    Cost.ticks (eqb_c E rx ry) +
    if eqb E rx ry then Cost.ticks (touch_c E rx uf2)
    else
      Cost.ticks (rank_of_c E uf2 rx) + Cost.ticks (rank_of_c E uf2 ry) +
      match Nat.compare (rank_of E uf2 rx) (rank_of E uf2 ry) with
      | Lt => Cost.ticks (link_c E rx ry false uf2)
      | Gt => Cost.ticks (link_c E ry rx false uf2)
      | Eq => Cost.ticks (link_c E ry rx true uf2)
      end)%N.
Proof.
  unfold union_c; rewrite Cost.ticks_bind; fold (find E x uf).
  destruct (find E x uf) as [rx u1].
  rewrite Cost.ticks_bind; fold (find E y u1).
  destruct (find E y u1) as [ry u2].
  rewrite Cost.ticks_bind; fold (eqb E rx ry).
  destruct (eqb E rx ry); [lia|].
  rewrite !Cost.ticks_bind; fold (rank_of E u2 rx) (rank_of E u2 ry).
  destruct (Nat.compare (rank_of E u2 rx) (rank_of E u2 ry)); lia.
Qed.

Arguments make_c {K} : simpl never.
Arguments make {K} : simpl never.
Arguments rank_of_c {K} E uf x : simpl never.
Arguments rank_of {K} E uf x : simpl never.
Arguments redirect_c {K} E x root uf : simpl never.
Arguments redirect {K} E x root uf : simpl never.
Arguments find_fuel_c {K} E fuel x uf : simpl never.
Arguments find_fuel {K} E fuel x uf : simpl never.
Arguments find_c {K} E x uf : simpl never.
Arguments find {K} E x uf : simpl never.
Arguments touch_c {K} E x uf : simpl never.
Arguments touch {K} E x uf : simpl never.
Arguments link_c {K} E child root raise uf : simpl never.
Arguments link {K} E child root raise uf : simpl never.
Arguments union_c {K} E x y uf : simpl never.
Arguments union {K} E x y uf : simpl never.
Arguments equivb_c {K} E x y uf : simpl never.
Arguments equivb {K} E x y uf : simpl never.
Arguments keys_c {K} _ uf : simpl never.
Arguments keys {K} E uf : simpl never.
Arguments of_unions_c {K} E xs : simpl never.
Arguments of_unions {K} E xs : simpl never.

End UnionFind.
Import UnionFind.
