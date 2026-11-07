(** * Indexed control-flow of structured skeletons

    Slot keys identify alternatives and callbacks close over prepared maps.
    For example, a conditional jump has separate taken and skipped slots.
    Builds on: ProgramSkeletonMachine, ProgramCfg and BaseMap. *)

From Stdlib Require Import List Bool Arith Lia PArith.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseCode BaseMap.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramSemantics ProgramCfg ProgramLink
  ProgramSkeleton ProgramSkeletonMachine.
Import List.ListNotations Cost.Notations Skeleton.

(** Points distinguish entering a statement from completing it. *)
Inductive skel_point : Type :=
  | PEntry (p : position)
  | PExit (p : position).

Definition point_key_c (v : skel_point) : Cost.t (position + position) :=
  Cost.ret
    (match v with
    | PEntry p => inl p
    | PExit p => inr p
    end).

(** Point encoding reuses the charged position-sum serializer. *)
Definition skel_point_encoding : encoding skel_point :=
  encoding_comap point_key_c (codec_enc (sum_codec position_codec position_codec)).

(** Position and phase together determine a unique point. *)
Theorem skel_point_encoding_laws : encoding_laws skel_point_encoding.
Proof.
  apply encoding_comap_laws.
  - intros [] [] Heq; inversion Heq; reflexivity.
  - apply codec_laws_injective, sum_codec_laws;
      apply list_codec_laws, derive_laws.
Qed.

(** Actions describe atom effects and branch observations. *)
Inductive skel_action (A G : Type) : Type :=
  | AAtom (a : A)
  | AGuard (g : G) (b : bool)
  | AIndexIs (g : G) (i : nat)
  | AIndexAtLeast (g : G) (len : nat)
  | AJump (p : position) (n : nat).
Arguments AAtom {A G}.
Arguments AGuard {A G}.
Arguments AIndexIs {A G}.
Arguments AIndexAtLeast {A G}.
Arguments AJump {A G}.

(** Edge identity contains its source and its slot, without client payloads. *)
Record skel_edge (A G : Type) : Type := SkelEdge {
  from : skel_point;
  slot : nat
}.
Arguments SkelEdge {A G}.
Arguments from {A G}.
Arguments slot {A G}.

Definition edge_key_c {A G} (e : skel_edge A G) : Cost.t (positive * nat) :=
  Cost.step ;;
  let* p := encode_c skel_point_encoding (from e) in
  Cost.ret (p, slot e).

(** Edge encoding preserves the point serializer's full charge. *)
Definition skel_edge_encoding {A G} : encoding (skel_edge A G) :=
  encoding_comap edge_key_c (codec_enc (pair_codec positive_codec nat_codec)).

(** Source and slot codes distinguish every edge key. *)
Theorem skel_edge_encoding_laws {A G} : encoding_laws (@skel_edge_encoding A G).
Proof.
  apply encoding_comap_laws.
  - intros [v i] [w j] Heq.
    change ((encode skel_point_encoding v, i) = (encode skel_point_encoding w, j)) in Heq.
    inversion Heq as [[Hv Hi]].
    apply (encode_injective skel_point_encoding_laws) in Hv; subst; reflexivity.
  - apply codec_laws_injective, pair_codec_laws.
    + apply positive_codec_laws.
    + apply nat_codec_laws.
Qed.

(** An action preserves its client events and branch-store equations. *)
Definition act_hold {A G St O} (C : skeleton_client A G St O) (x : skel_action A G)
    (st : St) (l : list O) (st' : St) : Prop :=
  match x with
  | AAtom a => atom_step C a st l st'
  | AGuard g b => guard_bool C g st = Some b /\ l = [] /\ st' = st
  | AIndexIs g i => guard_index C g st = Some i /\ l = [] /\ st' = st
  | AIndexAtLeast g len =>
    (exists j, guard_index C g st = Some j /\ len <= j) /\ l = [] /\ st' = st
  | AJump p n => jump_effect C p n st st' /\ l = []
  end.

(** Action lists compose store transitions and concatenate their events. *)
Inductive acts_hold {A G St O} (C : skeleton_client A G St O) :
    list (skel_action A G) -> St -> list O -> St -> Prop :=
  | holds_nil : forall st, acts_hold C [] st [] st
  | holds_cons : forall x xs st l1 st1 l2 st2,
      act_hold C x st l1 st1 -> acts_hold C xs st1 l2 st2 ->
      acts_hold C (x :: xs) st (l1 ++ l2) st2.
Arguments holds_nil {A G St O C}.
Arguments holds_cons {A G St O C}.

Definition machine_point {St} (m : mstate St) : skel_point :=
  match m with
  | Go p _ _ => PEntry p
  | Ret p _ _ => PExit p
  end.

(** Resuming a relative label has a store-independent destination. *)
Fixpoint resume_target_c (n : nat) (k : list frame) : Cost.t (option skel_point) :=
  Cost.step ;;
  match k with
  | [] => Cost.ret None
  | FSeq _ :: k | FJoin _ :: k => resume_target_c n k
  | FBlock p :: k =>
    match n with
    | 0 => Cost.ret (Some (PExit p))
    | S n => resume_target_c n k
    end
  | FLoop p :: k =>
    match n with
    | 0 => Cost.map (fun q => Some (PEntry q)) (app_c p [DBody])
    | S n => resume_target_c n k
    end
  end.

Definition resume_target n k := Cost.value (resume_target_c n k).

(** Target computation follows precisely the labelled-frame rules of the machine. *)
Theorem resume_target_equation n k :
  resume_target n k =
    match k with
    | [] => None
    | FSeq _ :: k | FJoin _ :: k => resume_target n k
    | FBlock p :: k =>
      match n with 0 => Some (PExit p) | S n => resume_target n k end
    | FLoop p :: k =>
      match n with 0 => Some (PEntry (p ++ [DBody])) | S n => resume_target n k end
    end.
Proof.
  unfold resume_target.
  destruct k as [|f k]; [reflexivity|]; destruct f; destruct n;
    cbn [resume_target_c]; autorewrite with galois_cost; reflexivity.
Qed.

(** Proper prefixes retain their labels even if a later direction is invalid. *)
Fixpoint enclosing_from {A G} (s : stmt A G) (base p : position) (k : list frame) :
    list frame :=
  match p with
  | [] => k
  | d :: p =>
    match child s d with
    | Some t => enclosing_from t (base ++ [d]) p (child_frame s d base :: k)
    | None =>
      match s with
      | Block _ => FBlock base :: k
      | Loop _ => FLoop base :: k
      | _ => k
      end
    end
  end.

Definition label_point {A G} (prog : stmt A G) p n :=
  resume_target n (enclosing_from prog [] p []).

(** Missing jump labels contribute no edge. *)
Definition jump_out_c {A G} k (p : position) n (xs : list (skel_action A G)) :
    Cost.t (list (skel_point * list (skel_action A G))) :=
  Cost.map
    (fun target => match target with Some v => [(v, xs)] | None => [] end)
    (resume_target_c n k).

(** Table construction visits each alternative once and retains duplicate targets. *)
Fixpoint table_out_c {A G} k p g (ns : list nat) (i : nat) :
    Cost.t (list (skel_point * list (skel_action A G))) :=
  match ns with
  | [] => Cost.ret []
  | n :: ns =>
    Cost.step ;;
    let* here := jump_out_c k p n [AIndexIs g i; AJump p n] in
    let* rest := table_out_c k p g ns (S i) in
    app_c here rest
  end.

(** Returning uses the nearest owner's continuation. *)
Definition return_point_c (f : frame) : Cost.t skel_point :=
  match f with
  | FSeq p => Cost.map PEntry (app_c p [DSecond])
  | FJoin p | FBlock p => Cost.ret (PExit p)
  | FLoop p => Cost.map PEntry (app_c p [DBody])
  end.

Definition return_point f := Cost.value (return_point_c f).

(** Local outgoing construction uses the already located subtree and its ancestor stack. *)
Definition entry_out_c {A G} (s : stmt A G) p k :
    Cost.t (list (skel_point * list (skel_action A G))) :=
  match s with
  | Atom a => Cost.ret [(PExit p, [AAtom a])]
  | Seq _ _ => Cost.map (fun q => [(PEntry q, [])]) (app_c p [DFirst])
  | If g _ _ =>
    let* first := app_c p [DFirst] in
    let* second := app_c p [DSecond] in
    Cost.ret [(PEntry first, [AGuard g true]); (PEntry second, [AGuard g false])]
  | Block _ | Loop _ => Cost.map (fun q => [(PEntry q, [])]) (app_c p [DBody])
  | Jump n => jump_out_c k p n [AJump p n]
  | JumpIf g n =>
    let* taken := jump_out_c k p n [AGuard g true; AJump p n] in
    app_c taken [(PExit p, [AGuard g false])]
  | JumpTable g ns n =>
    let* choices := table_out_c k p g ns 0 in
    let* len := length_c ns in
    let* default := jump_out_c k p n [AIndexAtLeast g len; AJump p n] in
    app_c choices default
  end.

Definition entry_out {A G} (s : stmt A G) p k := Cost.value (entry_out_c s p k).

(** The reference selector retains malformed-position and invalid-label behaviour. *)
Definition skel_out {A G} (prog : stmt A G) (v : skel_point) :
    list (skel_point * list (skel_action A G)) :=
  match v with
  | PEntry p =>
    match sub prog p with
    | Some s => entry_out s p (enclosing_from prog [] p [])
    | None => []
    end
  | PExit p =>
    match locate prog p with
    | Some (_, f :: _) => [(return_point f, [])]
    | _ => []
    end
  end.

Local Lemma enclosing_locate {A G} (s : stmt A G) base p k t k' :
  locate_from s base p k = Some (t, k') -> enclosing_from s base p k = k'.
Proof.
  revert s base k; induction p as [|d p IH]; intros s base k Hloc.
  - cbn in Hloc; inversion Hloc; reflexivity.
  - cbn [locate_from] in Hloc; cbn [enclosing_from].
    destruct (child s d) as [u|]; [eapply IH; exact Hloc|discriminate].
Qed.

(** A syntax row retains one subtree, its context and its two point ranks. *)
Record syntax_row (A G : Type) := SyntaxRow {
  row_position : position;
  row_statement : stmt A G;
  row_stack : list frame;
  row_entry_rank : nat;
  row_exit_rank : nat
}.
Arguments SyntaxRow {A G}.
Arguments row_position {A G}.
Arguments row_statement {A G}.
Arguments row_stack {A G}.
Arguments row_entry_rank {A G}.
Arguments row_exit_rank {A G}.

(** One syntax traversal computes preorder rows and entry/exit ranks.
    The returned counter is the first rank after the subtree.
    Child spans are obtained from returned counters and are never recomputed. *)
Fixpoint syntax_rows_c {A G} (s : stmt A G) p k (rank : nat) :
    Cost.t (list (syntax_row A G) * nat) :=
  Cost.step ;;
  match s with
  | Seq a b | If _ a b =>
    let* pa := app_c p [DFirst] in
    let* lhs := syntax_rows_c a pa (child_frame s DFirst p :: k) (S rank) in
    let* pb := app_c p [DSecond] in
    let* rhs := syntax_rows_c b pb (FJoin p :: k) (snd lhs) in
    let* children := app_c (fst lhs) (fst rhs) in
    Cost.ret (SyntaxRow p s k rank (snd rhs) :: children, S (snd rhs))
  | Block a | Loop a =>
    let* pa := app_c p [DBody] in
    let* body := syntax_rows_c a pa (child_frame s DBody p :: k) (S rank) in
    Cost.ret (SyntaxRow p s k rank (snd body) :: fst body, S (snd body))
  | _ => Cost.ret ([SyntaxRow p s k rank (S rank)], S (S rank))
  end.

Definition syntax_rows {A G} (s : stmt A G) p k rank := Cost.value (syntax_rows_c s p k rank).

(** The preparation equation exposes structure without exposing monad implementation details. *)
Theorem syntax_rows_equation {A G} (s : stmt A G) p k rank :
  syntax_rows s p k rank =
    match s with
    | Seq a b | If _ a b =>
      let left := syntax_rows a (p ++ [DFirst]) (child_frame s DFirst p :: k) (S rank) in
      let right := syntax_rows b (p ++ [DSecond]) (FJoin p :: k) (snd left) in
      (SyntaxRow p s k rank (snd right) :: fst left ++ fst right, S (snd right))
    | Block a | Loop a =>
      let body := syntax_rows a (p ++ [DBody]) (child_frame s DBody p :: k) (S rank) in
      (SyntaxRow p s k rank (snd body) :: fst body, S (snd body))
    | _ => ([SyntaxRow p s k rank (S rank)], S (S rank))
    end.
Proof.
  destruct s; unfold syntax_rows at 1; cbn [syntax_rows_c];
    autorewrite with galois_cost; reflexivity.
Qed.

(** Cached row positions enumerate a subtree in preorder with the supplied prefix. *)
Theorem syntax_rows_positions {A G} (s : stmt A G) p k rank :
  map row_position (fst (syntax_rows s p k rank)) = map (app p) (positions s).
Proof.
  revert p k rank; induction s; intros p k rank; rewrite syntax_rows_equation;
    cbn [fst positions map row_position].
  all: rewrite ?map_app, ?IHs1, ?IHs2, ?IHs, ?map_map.
  all: rewrite ?app_nil_r.
  all: f_equal.
  all: try (apply map_ext; intro q; rewrite <- app_assoc; reflexivity).
  all: f_equal; apply map_ext; intro q; rewrite <- app_assoc; reflexivity.
Qed.

(** A statement reserves one entry rank and one exit rank around its children. *)
Fixpoint statement_span {A G} (s : stmt A G) : nat :=
  match s with
  | Seq a b | If _ a b => 2 + statement_span a + statement_span b
  | Block a | Loop a => 2 + statement_span a
  | _ => 2
  end.

(** Preparation's counter consumes exactly the specified subtree span. *)
Theorem syntax_rows_span {A G} (s : stmt A G) p k rank :
  snd (syntax_rows s p k rank) = rank + statement_span s.
Proof.
  revert p k rank; induction s; intros p k rank; rewrite syntax_rows_equation;
    cbn [snd statement_span]; rewrite ?IHs1, ?IHs2, ?IHs; lia.
Qed.

(** Every retained subtree and stack agrees with its position in the original program. *)
Theorem syntax_rows_context {A G} (prog s : stmt A G) p k rank :
  context prog p k -> sub prog p = Some s ->
  forall r, In r (fst (syntax_rows s p k rank)) ->
    context prog (row_position r) (row_stack r) /\
      sub prog (row_position r) = Some (row_statement r).
Proof.
  revert p k rank; induction s; intros p k rank Hctx Hsub r Hin;
    rewrite syntax_rows_equation in Hin; cbn [fst] in Hin;
    destruct Hin as [<-|Hin].
  all: try solve [split; assumption].
  all: try contradiction.
  all: try (apply in_app_or in Hin; destruct Hin as [Hin|Hin]).
  all: first [eapply IHs1 in Hin|eapply IHs2 in Hin|eapply IHs in Hin].
  all: try exact Hin.
  all: try solve [lazymatch type of Hsub with
    | _ = Some ?owner =>
      first
        [eapply (context_child (s := owner) (d := DFirst))
        |eapply (context_child (s := owner) (d := DSecond))
        |eapply (context_child (s := owner) (d := DBody))];
      [exact Hctx|exact Hsub|reflexivity]
    end].
  all: rewrite (sub_child _ _ _ _ Hsub); reflexivity.
Qed.

(** Numbering retains every outgoing alternative's payload. *)
Fixpoint numbered_out_c {A G} (v : skel_point) (i : nat)
    (xs : list (skel_point * list (skel_action A G))) :
    Cost.t (list (skel_edge A G * (skel_point * list (skel_action A G)))) :=
  match xs with
  | [] => Cost.ret []
  | x :: xs =>
    Cost.step ;;
    Cost.map (cons (SkelEdge v i, x)) (numbered_out_c v (S i) xs)
  end.

Definition numbered_out {A G} v i (xs : list (skel_point * list (skel_action A G))) :=
  Cost.value (numbered_out_c v i xs).

(** Numbered alternatives retain their payload and advance the slot at every cell. *)
Theorem numbered_out_equation {A G} v i (xs : list (skel_point * list (skel_action A G))) :
  numbered_out v i xs =
    match xs with
    | [] => []
    | x :: rest => (SkelEdge v i, x) :: numbered_out v (S i) rest
    end.
Proof.
  destruct xs; reflexivity.
Qed.

(** Numbered keys are dense slots in the same order as the alternatives. *)
Theorem numbered_out_keys {A G} v i (xs : list (skel_point * list (skel_action A G))) :
  map fst (numbered_out v i xs) = map (SkelEdge v) (seq i (length xs)).
Proof.
  revert i; induction xs as [|x xs IH]; intro i.
  - reflexivity.
  - unfold numbered_out at 1; cbn [numbered_out_c].
    autorewrite with galois_cost.
    fold (@numbered_out A G v (S i) xs).
    cbn [map seq length fst]; rewrite IH; reflexivity.
Qed.

(** Prepared graph and payload tables share the same numbered alternatives. *)
Record skeleton_tables (A G : Type) := SkeletonIndex {
  indexed_positions : list position;
  indexed_nodes : list skel_point;
  indexed_out : Map.t skel_point (list (skel_edge A G));
  indexed_payload : Map.t (skel_edge A G) (skel_point * list (skel_action A G));
  indexed_rank : Map.t skel_point nat;
  indexed_span : nat
}.
Arguments SkeletonIndex {A G}.
Arguments indexed_positions {A G}.
Arguments indexed_nodes {A G}.
Arguments indexed_out {A G}.
Arguments indexed_payload {A G}.
Arguments indexed_rank {A G}.
Arguments indexed_span {A G}.

Definition row_out_c {A G} (r : syntax_row A G) :=
  let p := row_position r in
  let* entry := entry_out_c (row_statement r) p (row_stack r) in
  let* entering := numbered_out_c (PEntry p) 0 entry in
  let* exiting :=
    match row_stack r with
    | [] => Cost.ret []
    | f :: _ => Cost.map (fun v => [(v, [])]) (return_point_c f)
    end in
  let* leaving := numbered_out_c (PExit p) 0 exiting in
  Cost.ret [(PEntry p, entering); (PExit p, leaving)].

(** A valid syntax row produces exactly the two reference outgoing tables. *)
Theorem row_out_agrees {A G} (prog : stmt A G) (r : syntax_row A G) :
  context prog (row_position r) (row_stack r) ->
  sub prog (row_position r) = Some (row_statement r) ->
  Cost.value (row_out_c r) =
    [(PEntry (row_position r),
      numbered_out (PEntry (row_position r)) 0 (skel_out prog (PEntry (row_position r))));
     (PExit (row_position r),
      numbered_out (PExit (row_position r)) 0 (skel_out prog (PExit (row_position r))))].
Proof.
  destruct r as [p s k rank exit]; cbn [row_position row_stack row_statement].
  intros Hctx Hsub.
  destruct (context_locate prog p k Hctx) as [t [Hloc Hlookup]].
  assert (t = s) by congruence; subst t.
  pose proof (enclosing_locate prog [] p [] s k Hloc) as Henclosing.
  cbn [skel_out]; rewrite Hsub, Hloc, Henclosing.
  unfold row_out_c; cbn [row_position row_stack row_statement].
  repeat rewrite Cost.value_bind; rewrite Cost.value_ret.
  destruct k as [|f k]; [reflexivity|].
  rewrite Cost.value_map; reflexivity.
Qed.

Local Lemma flat_map_ext_in {X Y} (f g : X -> list Y) xs :
  (forall x, In x xs -> f x = g x) -> flat_map f xs = flat_map g xs.
Proof.
  intro H; induction xs as [|x xs IH]; [reflexivity|].
  cbn [flat_map]; rewrite H by (left; reflexivity).
  rewrite IH; [reflexivity|intros y Hin; apply H; right; exact Hin].
Qed.

Local Lemma flat_map_project {X Y Z} (f : Y -> list Z) (g : X -> Y) xs :
  flat_map (fun x => f (g x)) xs = flat_map f (map g xs).
Proof.
  induction xs as [|x xs IH]; cbn [flat_map map]; rewrite ?IH; reflexivity.
Qed.

(** Prepared outgoing rows agree with the reference selector in position order. *)
Theorem prepared_rows_agree {A G} (prog : stmt A G) :
  flat_map (fun r => Cost.value (row_out_c r)) (fst (syntax_rows prog [] [] 0)) =
    flat_map (fun p =>
      [(PEntry p, numbered_out (PEntry p) 0 (skel_out prog (PEntry p)));
       (PExit p, numbered_out (PExit p) 0 (skel_out prog (PExit p)))]) (positions prog).
Proof.
  transitivity
    (flat_map (fun r =>
      [(PEntry (row_position r),
        numbered_out (PEntry (row_position r)) 0 (skel_out prog (PEntry (row_position r))));
       (PExit (row_position r),
        numbered_out (PExit (row_position r)) 0 (skel_out prog (PExit (row_position r))))])
      (fst (syntax_rows prog [] [] 0))).
  - apply flat_map_ext_in; intros r Hin.
    destruct (syntax_rows_context prog prog [] [] 0 context_root eq_refl r Hin)
      as [Hctx Hsub].
    apply row_out_agrees; assumption.
  - rewrite (flat_map_project (fun p =>
      [(PEntry p, numbered_out (PEntry p) 0 (skel_out prog (PEntry p)));
       (PExit p, numbered_out (PExit p) 0 (skel_out prog (PExit p)))])
      (@row_position A G)).
    rewrite syntax_rows_positions, map_id; reflexivity.
Qed.

(** Charged concatenation visits every outer cell and copies every returned inner list. *)
Definition skeleton_flat_map_c {X Y} (f : X -> Cost.t (list Y)) (xs : list X) :=
  fold_right_c (fun x rest => let* ys := f x in app_c ys rest) [] xs.

Local Lemma skeleton_flat_map_value {X Y} (f : X -> Cost.t (list Y)) xs :
  Cost.value (skeleton_flat_map_c f xs) = flat_map (fun x => Cost.value (f x)) xs.
Proof.
  unfold skeleton_flat_map_c; rewrite value_fold_right_c.
  induction xs as [|x xs IH]; [reflexivity|].
  cbn [fold_right flat_map]; rewrite Cost.value_bind, value_app_c, IH; reflexivity.
Qed.

Local Lemma skeleton_map_value {X Y} (f : X -> Cost.t Y) (g : X -> Y) xs :
  (forall x, Cost.value (f x) = g x) -> Cost.value (map_c f xs) = map g xs.
Proof.
  intro Hvalue; rewrite value_map_c; apply map_ext; exact Hvalue.
Qed.

Definition row_keys_c {A G}
    (row : skel_point * list (skel_edge A G * (skel_point * list (skel_action A G)))) :=
  Cost.map (fun keys => (fst row, keys)) (map_c (fun e => Cost.ret (fst e)) (snd row)).

Local Lemma row_keys_value {A G}
    (row : skel_point * list (skel_edge A G * (skel_point * list (skel_action A G)))) :
  Cost.value (row_keys_c row) = (fst row, map fst (snd row)).
Proof.
  unfold row_keys_c; rewrite Cost.value_map, value_map_c; reflexivity.
Qed.

(** Preparation traverses syntax once, then builds maps from the retained rows. *)
Definition skeleton_index_c {A G} (s : stmt A G) : Cost.t (skeleton_tables A G) :=
  let* prepared := syntax_rows_c s [] [] 0 in
  let* ps := map_c (fun r => Cost.ret (row_position r)) (fst prepared) in
  let* ns := skeleton_flat_map_c (fun p => Cost.ret [PEntry p; PExit p]) ps in
  let* rows := skeleton_flat_map_c row_out_c (fst prepared) in
  let* out_rows := map_c row_keys_c rows in
  let* payload_rows := skeleton_flat_map_c (fun row => Cost.ret (snd row)) rows in
  let* ranks := skeleton_flat_map_c (fun r =>
    Cost.ret [(PEntry (row_position r), row_entry_rank r);
      (PExit (row_position r), row_exit_rank r)]) (fst prepared) in
  let* outs := Map.of_list_c skel_point_encoding out_rows in
  let* payloads := Map.of_list_c skel_edge_encoding payload_rows in
  let* rank_table := Map.of_list_c skel_point_encoding ranks in
  Cost.ret (SkeletonIndex ps ns outs payloads rank_table (snd prepared)).

Definition skeleton_index {A G} (s : stmt A G) := Cost.value (skeleton_index_c s).

(** Preparation exposes its exact row-to-map construction for arbitrary syntax. *)
Theorem skeleton_index_equation {A G} (s : stmt A G) :
  skeleton_index s =
    let prepared := syntax_rows s [] [] 0 in
    let ps := map row_position (fst prepared) in
    let rows := flat_map (fun r => Cost.value (row_out_c r)) (fst prepared) in
    SkeletonIndex ps (flat_map (fun p => [PEntry p; PExit p]) ps)
      (Map.of_list skel_point_encoding (map (fun row => (fst row, map fst (snd row))) rows))
      (Map.of_list skel_edge_encoding (flat_map snd rows))
      (Map.of_list skel_point_encoding
        (flat_map (fun r => [(PEntry (row_position r), row_entry_rank r);
          (PExit (row_position r), row_exit_rank r)]) (fst prepared)))
      (snd prepared).
Proof.
  unfold skeleton_index, skeleton_index_c.
  repeat rewrite Cost.value_bind.
  rewrite Cost.value_ret.
  fold (syntax_rows s [] [] 0).
  destruct (syntax_rows s [] [] 0) as [rs span]; cbn [fst snd].
  rewrite (skeleton_map_value _ row_position rs) by reflexivity.
  rewrite !skeleton_flat_map_value.
  rewrite (skeleton_map_value _ _ _ (@row_keys_value A G)).
  reflexivity.
Qed.

(** Preparation establishes the map invariants without requiring any client proof. *)
Theorem prepared_skeleton_wf {A G} (s : stmt A G) :
  Map.wf skel_point_encoding (indexed_out (skeleton_index s)) /\
  Map.wf skel_edge_encoding (indexed_payload (skeleton_index s)) /\
  Map.wf skel_point_encoding (indexed_rank (skeleton_index s)).
Proof.
  rewrite skeleton_index_equation; cbn [indexed_out indexed_payload indexed_rank].
  repeat split; apply Map.wf_of_list.
Qed.

(** The cached positions equal the complete duplicate-free syntactic enumeration. *)
Theorem indexed_positions_exact {A G} (s : stmt A G) :
  indexed_positions (skeleton_index s) = positions s.
Proof.
  rewrite skeleton_index_equation; cbn [indexed_positions].
  rewrite syntax_rows_positions; apply map_id.
Qed.

Definition indexed_keys_c {A G} (index : skeleton_tables A G) v :=
  Map.find_or_c skel_point_encoding [] v (indexed_out index).

Definition indexed_keys {A G} (index : skeleton_tables A G) v :=
  Cost.value (indexed_keys_c index v).

Definition indexed_to_c {A G} (index : skeleton_tables A G) (e : skel_edge A G) :=
  Cost.map
    (fun payload => match payload with Some (t, _) => t | None => from e end)
    (Map.get_c skel_edge_encoding e (indexed_payload index)).

Definition indexed_to {A G} (index : skeleton_tables A G) e :=
  Cost.value (indexed_to_c index e).

Definition indexed_acts_c {A G} (index : skeleton_tables A G) (e : skel_edge A G) :=
  Cost.map
    (fun payload => match payload with Some (_, xs) => xs | None => [] end)
    (Map.get_c skel_edge_encoding e (indexed_payload index)).

Definition indexed_acts {A G} (index : skeleton_tables A G) e :=
  Cost.value (indexed_acts_c index e).

(** Rank lookup reports absent points explicitly. *)
Definition indexed_point_rank_c {A G} (index : skeleton_tables A G) v :=
  Map.get_c skel_point_encoding v (indexed_rank index).

Definition indexed_point_rank {A G} (index : skeleton_tables A G) v :=
  Cost.value (indexed_point_rank_c index v).

(** Missing point keys have no outgoing edges. *)
Theorem indexed_keys_equation {A G} (index : skeleton_tables A G) v :
  indexed_keys index v =
    match Map.get skel_point_encoding v (indexed_out index) with
    | Some es => es
    | None => []
    end.
Proof.
  apply Map.find_or_equation.
Qed.

(** Missing edge keys target their own source. *)
Theorem indexed_to_equation {A G} (index : skeleton_tables A G) e :
  indexed_to index e =
    match Map.get skel_edge_encoding e (indexed_payload index) with
    | Some (t, _) => t
    | None => from e
    end.
Proof.
  unfold indexed_to, indexed_to_c; rewrite Cost.value_map; reflexivity.
Qed.

(** Missing edge keys have no actions. *)
Theorem indexed_acts_equation {A G} (index : skeleton_tables A G) e :
  indexed_acts index e =
    match Map.get skel_edge_encoding e (indexed_payload index) with
    | Some (_, xs) => xs
    | None => []
    end.
Proof.
  unfold indexed_acts, indexed_acts_c; rewrite Cost.value_map; reflexivity.
Qed.

(** Graph callbacks retain the charged map lookups and share the same prepared index. *)
Definition indexed_graph {A G} (index : skeleton_tables A G) :
    Graph.t skel_point (skel_edge A G) :=
  Graph.Make [PEntry []] (indexed_nodes index) (indexed_keys_c index)
    (fun e => Cost.ret (from e)) (indexed_to_c index).

(** CFG construction runs preparation once before closing over its tables. *)
Definition skeleton_cfg_c {A G} (s : stmt A G) : Cost.t (Cfg.t skel_point (skel_edge A G)) :=
  Cost.map (fun index =>
    Cfg.Make (indexed_graph index) skel_point_encoding skel_edge_encoding) (skeleton_index_c s).

Definition skeleton_cfg {A G} (s : stmt A G) := Cost.value (skeleton_cfg_c s).

(** A skeleton CFG's fields are observations of its one prepared index. *)
Theorem skeleton_cfg_equation {A G} (s : stmt A G) :
  skeleton_cfg s =
    Cfg.Make (indexed_graph (skeleton_index s)) skel_point_encoding skel_edge_encoding.
Proof.
  reflexivity.
Qed.

(** Graph nodes contain both phases of every valid position in legacy order. *)
Theorem skeleton_cfg_nodes {A G} (s : stmt A G) :
  Graph.nodes (Cfg.graph (skeleton_cfg s)) =
    flat_map (fun p => [PEntry p; PExit p]) (positions s).
Proof.
  rewrite skeleton_cfg_equation, skeleton_index_equation.
  cbn [Cfg.graph indexed_graph Graph.nodes indexed_nodes].
  rewrite syntax_rows_positions, map_id; reflexivity.
Qed.

Definition skel_to {A G} (s : stmt A G) := indexed_to (skeleton_index s).
Definition skel_acts {A G} (s : stmt A G) := indexed_acts (skeleton_index s).

(** Loop heads are body entries of loops, in statement preorder. *)
Definition loop_heads {A G} (prog : stmt A G) : list skel_point :=
  flat_map (fun p =>
    match sub prog p with
    | Some (Loop _) => [PEntry (p ++ [DBody])]
    | _ => []
    end) (positions prog).

(** Splitting a position separates its final direction from its proper prefix. *)
Fixpoint split_last (p : position) : option (position * dir) :=
  match p with
  | [] => None
  | d :: [] => Some ([], d)
  | d :: rest =>
    match split_last rest with
    | Some (base, last) => Some (d :: base, last)
    | None => None
    end
  end.

(** A body entry is a loop head when its owner is a loop. *)
Definition is_loop_head {A G} (prog : stmt A G) (n : skel_point) : bool :=
  match n with
  | PEntry p =>
    match split_last p with
    | Some (base, DBody) =>
      match sub prog base with
      | Some (Loop _) => true
      | _ => false
      end
    | _ => false
    end
  | PExit _ => false
  end.

(** The link associates an actual store transition with a listed slot and its actions. *)
Definition skeleton_link {A G St O} (prog : stmt A G) (C : skeleton_client A G St O) :
    Link.t (mstate St) O skel_point (skel_edge A G) :=
  let index := skeleton_index prog in
  Link.Make machine_point
    (fun m l m' e =>
      In e (indexed_keys index (machine_point m)) /\
      machine_point m' = indexed_to index e /\
      acts_hold C (indexed_acts index e) (store_of m) l (store_of m'))
    (fun _ _ _ => False).

Arguments skeleton_cfg {A G} s : simpl never.
Arguments skeleton_index {A G} s : simpl never.
