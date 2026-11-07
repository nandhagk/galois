(** * Shared transfer dispatch

    Empty operands and concrete points take priority over domain-specific entries.
    For example, an empty table still evaluates addition on singleton operands.
    Builds on: DomainsValue and CostList. *)

From Stdlib Require Import List Bool ZArith.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Lattice Require Import LatticeCore LatticeConcrete.
From Galois.Bits Require Import BitsWord BitsOp.
From Galois.Domains Require Import DomainsValue DomainsNumeric.
Import List.ListNotations Cost.Notations.

Module Transfer.

(** Entries are indexed by operator and operand count and receive ordered operand lists. *)
Record table (A B K R : Type) : Type := Make {
  fwd : K -> nat -> Cost.t (option (R -> list A -> Cost.t B));
  bwd : K -> nat -> Cost.t (option (R -> B -> list A -> Cost.t (list B)))
}.

Arguments fwd {A B K R}.
Arguments bwd {A B K R}.

(** Shape callbacks separate operand, result and context representations. *)
Record shape (A B K R C : Type) : Type := Shape {
  eval_c : K -> list C -> Cost.t (option C);
  point_c : A -> Cost.t (option C);
  is_empty_c : A -> Cost.t bool;
  inj_c : R -> C -> Cost.t B;
  bot_out : R -> B;
  top_out : R -> B;
  keep_c : A -> Cost.t B
}.

Arguments eval_c {A B K R C}.
Arguments point_c {A B K R C}.
Arguments is_empty_c {A B K R C}.
Arguments inj_c {A B K R C}.
Arguments bot_out {A B K R C}.
Arguments top_out {A B K R C}.
Arguments keep_c {A B K R C}.

(** Concrete evaluation is the value of the shape's charged callback. *)
Definition eval {A B K R C} (S : shape A B K R C) k xs := Cost.value (eval_c S k xs).

(** Collecting points stops on the first non-singleton operand. *)
Fixpoint points_c {A B K R C} (S : shape A B K R C) (xs : list A)
    : Cost.t (option (list C)) :=
  match xs with
  | [] => Cost.ret (Some [])
  | x :: xs =>
    Cost.step ;;
    let* p := Cost.step ;; point_c S x in
    match p with
    | None => Cost.ret None
    | Some c =>
      Cost.map (fun cs =>
        match cs with
        | Some cs => Some (c :: cs)
        | None => None
        end) (points_c S xs)
    end
  end.

(** Dispatch charges the arity scan, lookup and selected callback. *)
Definition dispatch_c {A B K R C} (T : table A B K R) (S : shape A B K R C)
    k r xs : Cost.t B :=
  let* n := length_c xs in
  let* entry := Cost.step ;; fwd T k n in
  match entry with
  | Some f => Cost.step ;; f r xs
  | None => Cost.ret (top_out S r)
  end.

(** Forward transfer prioritizes empty operands, then points, then an arity entry. *)
Definition forward_c {A B K R C} (T : table A B K R) (S : shape A B K R C)
    k r xs : Cost.t B :=
  let* empty := existsb_c (fun x => Cost.step ;; is_empty_c S x) xs in
  if empty then Cost.ret (bot_out S r) else
  let* points := points_c S xs in
  match points with
  | Some cs =>
    let* result := Cost.step ;; eval_c S k cs in
    match result with
    | Some c => Cost.step ;; inj_c S r c
    | None => Cost.ret (bot_out S r)
    end
  | None => dispatch_c T S k r xs
  end.

(** Pure forward transfer observes the charged dispatch. *)
Definition forward {A B K R C} (T : table A B K R) (S : shape A B K R C) k r xs :=
  Cost.value (forward_c T S k r xs).

(** Backward transfer uses the arity entry or a charged map of the default embedding. *)
Definition backward_c {A B K R C} (T : table A B K R) (S : shape A B K R C)
    k r a xs : Cost.t (list B) :=
  let* n := length_c xs in
  let* entry := Cost.step ;; bwd T k n in
  match entry with
  | Some f => Cost.step ;; f r a xs
  | None => map_c (fun x => Cost.step ;; keep_c S x) xs
  end.

(** Pure backward transfer observes the charged dispatch. *)
Definition backward {A B K R C} (T : table A B K R) (S : shape A B K R C) k r a xs :=
  Cost.value (backward_c T S k r a xs).

End Transfer.

(** Shape laws relate singleton observations, empty tests and embeddings to concrete meaning. *)
Record transfer_sem {A B K R C} (S : Transfer.shape A B K R C)
    (gA : A -> C -> Prop) (gB : R -> B -> C -> Prop) (ctx_ok : R -> C -> Prop)
    : Prop := {
  point_sound : forall x c d, Cost.value (Transfer.point_c S x) = Some c -> gA x d ->
    c = d;
  empty_sound : forall x c, Cost.value (Transfer.is_empty_c S x) = true -> ~ gA x c;
  inj_sound : forall r c, ctx_ok r c -> gB r (Cost.value (Transfer.inj_c S r c)) c;
  bot_out_empty : forall r c, ~ gB r (Transfer.bot_out S r) c;
  top_out_full : forall r c, ctx_ok r c -> gB r (Transfer.top_out S r) c;
  keep_sound : forall r x c, gA x c -> gB r (Cost.value (Transfer.keep_c S x)) c
}.

Arguments point_sound {A B K R C S gA gB ctx_ok}.
Arguments empty_sound {A B K R C S gA gB ctx_ok}.
Arguments inj_sound {A B K R C S gA gB ctx_ok}.
Arguments top_out_full {A B K R C S gA gB ctx_ok}.
Arguments keep_sound {A B K R C S gA gB ctx_ok}.

(** Each supplied table entry proves soundness on exactly its declared arity. *)
Record table_laws {A B K R C} (T : Transfer.table A B K R)
    (S : Transfer.shape A B K R C) (gA : A -> C -> Prop)
    (gB : R -> B -> C -> Prop) (ctx_ok : R -> C -> Prop) : Prop := {
  fwd_sound : forall k n f r xs cs c,
    Cost.value (Transfer.fwd T k n) = Some f -> length xs = n ->
    Forall2 gA xs cs -> Transfer.eval S k cs = Some c -> ctx_ok r c ->
    gB r (Cost.value (f r xs)) c;
  bwd_sound : forall k n f r a xs cs c,
    Cost.value (Transfer.bwd T k n) = Some f -> length xs = n ->
    Forall2 gA xs cs -> Transfer.eval S k cs = Some c -> ctx_ok r c -> gB r a c ->
    Forall2 (gB r) (Cost.value (f r a xs)) cs;
  bwd_length : forall k n f r a xs,
    Cost.value (Transfer.bwd T k n) = Some f -> length xs = n ->
    length (Cost.value (f r a xs)) = length xs
}.

Arguments fwd_sound {A B K R C T S gA gB ctx_ok}.
Arguments bwd_sound {A B K R C T S gA gB ctx_ok}.
Arguments bwd_length {A B K R C T S gA gB ctx_ok}.

(** Structural refinement is proved per backward entry and for the default embedding. *)
Record table_refines {A B K R C} (T : Transfer.table A B K R)
    (S : Transfer.shape A B K R C) (rel : A -> B -> Prop) : Prop := {
  keep_refines : forall x, rel x (Cost.value (Transfer.keep_c S x));
  entry_refines : forall k n f r a xs,
    Cost.value (Transfer.bwd T k n) = Some f -> length xs = n ->
    Forall2 rel xs (Cost.value (f r a xs))
}.

Arguments keep_refines {A B K R C T S rel}.
Arguments entry_refines {A B K R C T S rel}.

(** Per-entry refinement and default refinement cover the whole backward dispatch. *)
Theorem backward_refines {A B K R C} (T : Transfer.table A B K R)
    (S : Transfer.shape A B K R C) rel :
  table_refines T S rel -> forall k r a xs,
  Forall2 rel xs (Transfer.backward T S k r a xs).
Proof.
  intros H k r a xs. unfold Transfer.backward, Transfer.backward_c.
  autorewrite with galois_cost.
  destruct (Cost.value (Transfer.bwd T k (length xs))) as [f|] eqn:Hf.
  - autorewrite with galois_cost. eapply (entry_refines H); eauto.
  - rewrite value_map_c. clear Hf.
    induction xs as [|x xs IH]; cbn; constructor.
    + exact (keep_refines H x).
    + exact IH.
Qed.

Section Soundness.
Context {A B K R C : Type} (T : Transfer.table A B K R)
  (S : Transfer.shape A B K R C) (gA : A -> C -> Prop)
  (gB : R -> B -> C -> Prop) (ctx_ok : R -> C -> Prop)
  (HS : transfer_sem S gA gB ctx_ok) (HT : table_laws T S gA gB ctx_ok).

Local Lemma no_empty xs cs : Forall2 gA xs cs ->
  existsb (fun x => Cost.value (Transfer.is_empty_c S x)) xs = false.
Proof.
  intros H. induction H as [|x c xs cs Hx Hxs IH]; cbn; [reflexivity|].
  destruct (Cost.value (Transfer.is_empty_c S x)) eqn:Hxempty; [|exact IH].
  exfalso. exact (empty_sound HS x c Hxempty Hx).
Qed.

Local Lemma points_agree xs cs : Forall2 gA xs cs -> forall ds,
  Cost.value (Transfer.points_c S xs) = Some ds -> ds = cs.
Proof.
  intros H. induction H as [|x c xs cs Hx Hxs IH]; intros ds Hp.
  - inversion Hp. reflexivity.
  - cbn [Transfer.points_c] in Hp. autorewrite with galois_cost in Hp.
    destruct (Cost.value (Transfer.point_c S x)) as [d|] eqn:Hd; [|discriminate].
    autorewrite with galois_cost in Hp.
    destruct (Cost.value (Transfer.points_c S xs)) as [tail|] eqn:Htail;
      [|discriminate].
    inversion Hp; subst ds. f_equal.
    + exact (point_sound HS x d c Hd Hx).
    + apply IH. reflexivity.
Qed.

(** Forward transfer retains every defined result under the supplied result context. *)
Theorem forward_sound k r xs cs c :
  Forall2 gA xs cs -> Transfer.eval S k cs = Some c -> ctx_ok r c ->
  gB r (Transfer.forward T S k r xs) c.
Proof.
  intros Hxs Heval Hctx. unfold Transfer.forward, Transfer.forward_c.
  autorewrite with galois_cost.
  change (existsb (fun x => Cost.value (Cost.step ;; Transfer.is_empty_c S x)) xs)
    with (existsb (fun x => Cost.value (Transfer.is_empty_c S x)) xs).
  rewrite (no_empty xs cs Hxs).
  destruct (Cost.value (Transfer.points_c S xs)) as [ds|] eqn:Hp.
  - pose proof (points_agree xs cs Hxs ds Hp) as ->.
    autorewrite with galois_cost.
    rewrite Hp. autorewrite with galois_cost.
    change (Cost.value (Transfer.eval_c S k cs)) with (Transfer.eval S k cs).
    rewrite Heval. autorewrite with galois_cost. apply (inj_sound HS), Hctx.
  - autorewrite with galois_cost. rewrite Hp.
    unfold Transfer.dispatch_c. autorewrite with galois_cost.
    destruct (Cost.value (Transfer.fwd T k (length xs))) as [f|] eqn:Hf.
    + autorewrite with galois_cost. eapply (fwd_sound HT); eauto.
    + apply (top_out_full HS), Hctx.
Qed.

(** Backward transfer retains every input producing a result that satisfies the result fact. *)
Theorem backward_sound k r a xs cs c :
  Forall2 gA xs cs -> Transfer.eval S k cs = Some c -> ctx_ok r c -> gB r a c ->
  Forall2 (gB r) (Transfer.backward T S k r a xs) cs.
Proof.
  intros Hxs Heval Hctx Ha. unfold Transfer.backward, Transfer.backward_c.
  autorewrite with galois_cost.
  destruct (Cost.value (Transfer.bwd T k (length xs))) as [f|] eqn:Hf.
  - autorewrite with galois_cost. eapply (bwd_sound HT); eauto.
  - rewrite value_map_c.
    change (Forall2 (gB r) (map (fun x => Cost.value (Transfer.keep_c S x)) xs) cs).
    clear Heval Hctx Ha Hf.
    induction Hxs as [|x d xs ds Hx Hxs IH]; cbn; constructor.
    + now apply (keep_sound HS).
    + exact IH.
Qed.

(** Backward transfer keeps the input operand count even without semantic witnesses. *)
Theorem backward_length k r a xs :
  length (Transfer.backward T S k r a xs) = length xs.
Proof.
  unfold Transfer.backward, Transfer.backward_c. autorewrite with galois_cost.
  destruct (Cost.value (Transfer.bwd T k (length xs))) as [f|] eqn:Hf.
  - autorewrite with galois_cost. eapply (bwd_length HT); eauto.
  - rewrite value_map_c, length_map. reflexivity.
Qed.
End Soundness.

(** Any detected empty operand forces the output bottom before table lookup. *)
Theorem forward_empty {A B K R C} (T : Transfer.table A B K R)
    (S : Transfer.shape A B K R C) k r xs :
  existsb (fun x => Cost.value (Transfer.is_empty_c S x)) xs = true ->
  Transfer.forward T S k r xs = Transfer.bot_out S r.
Proof.
  intro H. unfold Transfer.forward, Transfer.forward_c.
  autorewrite with galois_cost.
  change (existsb (fun x => Cost.value (Cost.step ;; Transfer.is_empty_c S x)) xs)
    with (existsb (fun x => Cost.value (Transfer.is_empty_c S x)) xs).
  now rewrite H.
Qed.

(** The all-point path evaluates concretely and maps failed evaluation to bottom. *)
Theorem forward_point {A B K R C} (T : Transfer.table A B K R)
    (S : Transfer.shape A B K R C) k r xs cs :
  existsb (fun x => Cost.value (Transfer.is_empty_c S x)) xs = false ->
  Cost.value (Transfer.points_c S xs) = Some cs ->
  Transfer.forward T S k r xs =
    match Transfer.eval S k cs with
    | Some c => Cost.value (Transfer.inj_c S r c)
    | None => Transfer.bot_out S r
    end.
Proof.
  intros He Hp. unfold Transfer.forward, Transfer.forward_c.
  autorewrite with galois_cost.
  change (existsb (fun x => Cost.value (Cost.step ;; Transfer.is_empty_c S x)) xs)
    with (existsb (fun x => Cost.value (Transfer.is_empty_c S x)) xs).
  rewrite He. autorewrite with galois_cost.
  rewrite Hp. autorewrite with galois_cost.
  unfold Transfer.eval. destruct (Cost.value (Transfer.eval_c S k cs));
    autorewrite with galois_cost; reflexivity.
Qed.

#[export] Hint Extern 5 (gamma _ (Transfer.forward _ _ _ _ _) _) =>
  eapply forward_sound : galois_gamma.
#[export] Hint Extern 5 (Forall2 _ (Transfer.backward _ _ _ _ _ _) _) =>
  eapply backward_sound : galois_gamma.

(** A table with no entries retains the shared point path and backward defaults. *)
Definition empty_table {A B K R} : Transfer.table A B K R :=
  {| Transfer.fwd := fun _ _ => Cost.ret None;
     Transfer.bwd := fun _ _ => Cost.ret None |}.

(** The open builder uses unit context and caller-supplied guard refinement. *)
Definition value_of_table {A K G C} (T : Transfer.table A A K unit)
    (S : Transfer.shape A A K unit C) (L : lattice A) (top : A)
    (guard : G -> list A -> Cost.t (list A)) : ValueAbs.t A K G :=
  {| ValueAbs.lat := L;
     ValueAbs.top := top;
     ValueAbs.op_c := fun k xs => Transfer.forward_c T S k tt xs;
     ValueAbs.back_c := fun k a xs => Transfer.backward_c T S k tt a xs;
     ValueAbs.guard_c := guard |}.

(** Word tables use the concrete operand width when interpreting backward payloads. *)
Definition word_output {P} (G : width -> P -> Z -> Prop) (_ : width) (p : P) (c : word) :=
  G (fst c) p (snd c).

(** Result context requires a normalized result at the requested width. *)
Definition word_context (w : width) (c : word) :=
  fst c = w /\ is_word (fst c) (snd c).

(** The word builder leaves meet and the payload lattice independent of transfer entries. *)
Definition word_of_table {P} (T : Transfer.table (width * P) P op width)
    (S : Transfer.shape (width * P) P op width word)
    (L : width -> lattice P) (top : width -> P)
    (constant : width -> Z -> Cost.t P) (meet : width -> P -> P -> Cost.t P)
    : word_domain P :=
  {| plat := L;
     ptop := top;
     pconst_c := constant;
     pforward_c := fun o xs rw => Transfer.forward_c T S o rw xs;
     passume_c := fun o xs rw a => Transfer.backward_c T S o rw a xs;
     pmeet_c := meet |}.

Local Lemma combine_backward {P} (G : width -> P -> Z -> Prop) xs cs qs :
  Forall2 (payload_sound G) xs cs ->
  Forall2 (fun p c => G (fst c) p (snd c)) qs cs ->
  Forall2 (fun p c => G (fst p) (snd p) (snd c))
    (combine (map fst xs) qs) cs.
Proof.
  intro H. revert qs.
  induction H as [|[w p] [v z] xs cs Hhead Htail IH]; intros qs Hqs.
  - inversion Hqs. constructor.
  - inversion Hqs as [|q c qs' cs' Hq Hrest]; subst.
    cbn. constructor.
    + pose proof (proj1 Hhead) as Hw. change (w = v) in Hw.
      cbn in Hq |- *. now rewrite Hw.
    + now apply IH.
Qed.

(** Shape and entry laws prove word soundness once under independent structural refinement. *)
Theorem word_of_table_laws {P} (T : Transfer.table (width * P) P op width)
    (S : Transfer.shape (width * P) P op width word)
    (L : width -> lattice P) top constant meet (G : width -> P -> Z -> Prop) :
  (forall o cs, Transfer.eval S o cs = eval_op o cs) ->
  transfer_sem S (payload_sound G) (word_output G) word_context ->
  table_laws T S (payload_sound G) (word_output G) word_context ->
  (forall w, lattice_laws (L w)) ->
  (forall w a b z, leb (L w) a b = true -> G w a z -> G w b z) ->
  (forall w z, ~ G w (bot (L w)) z) ->
  (forall w z, is_word w z -> G w (top w) z) ->
  (forall w z, G w (Cost.value (constant w z)) (wrap w z)) ->
  table_refines T S (fun wp q => leb (L (fst wp)) q (snd wp) = true) ->
  (forall w a b z, G w a z -> G w b z -> G w (Cost.value (meet w a b)) z) ->
  (forall w a b, leb (L w) (Cost.value (meet w a b)) a = true) ->
  word_laws (word_of_table T S L top constant meet) G.
Proof.
  intros Heval HS HT HL HG Hbot Htop Hconst Hback Hmeet Hlower. constructor.
  - exact HL.
  - exact HG.
  - exact Hbot.
  - exact Htop.
  - exact Hconst.
  - intros o xs cs rw z Hxs Hr.
    exact (forward_sound T S _ _ _ HS HT o rw xs cs (rw, z)
      Hxs (eq_trans (Heval o cs) Hr) (conj eq_refl (eval_op_is_word o cs (rw, z) Hr))).
  - intros o xs cs rw z a Hxs Hr Ha. apply combine_backward with (G := G).
    + exact Hxs.
    + exact (backward_sound T S _ _ _ HS HT o rw a xs cs (rw, z)
        Hxs (eq_trans (Heval o cs) Hr) (conj eq_refl (eval_op_is_word o cs (rw, z) Hr)) Ha).
  - intros. apply (backward_refines T S _ Hback).
  - exact Hmeet.
  - exact Hlower.
Qed.

Arguments Transfer.forward_c : simpl never.
Arguments Transfer.forward : simpl never.
Arguments Transfer.backward_c : simpl never.
Arguments Transfer.backward : simpl never.
