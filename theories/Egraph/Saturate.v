(** * Equality saturation

    The front end checks its inputs, adds their nodes and runs the compiled engine program.
    For example, literal children are stored as values while constructor roots return classes.
    Builds on: SaturateSig. *)

From Stdlib Require Import List PArith NArith Arith Lia Bool.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import Trie.
From Galois.Egglog Require Import ValueSig IndexSig JoinSig DatabaseSig RunSig Syntax Model Sorts
  ModelFacts.
From Galois.Egraph Require Import Syntax CompileSig SaturateSig.

Import List.ListNotations.

(** * Checking flat syntax *)

(** A node records its required sort and whether it is used by a later constructor. *)
Definition front_shape := (option sort * bool)%type.

Definition front_initial {V : Type} (n : pnode V) : front_shape :=
  (match n with
   | PHole _ => None
   | PApp _ _ => Some SId
   | PLit _ => Some SVal
   end, false).
TimeFun front_initial.

(** A constraint walks only the prefix named by its unary child index. *)
Fixpoint front_require (j : nat) (s : sort) (sh : list front_shape)
    : option (list front_shape) :=
  match sh, j with
  | [], _ => None
  | (old, _) :: rest, O =>
      match old with
      | None => Some ((Some s, true) :: rest)
      | Some t => if sort_eqb t s then Some ((Some s, true) :: rest) else None
      end
  | first :: rest, S j' =>
      match front_require j' s rest with
      | None => None
      | Some sh' => Some (first :: sh')
      end
  end.
TimeFun front_require.

Fixpoint front_require_children (i : nat) (children : list nat) (ss : list sort)
    (sh : list front_shape) : option (list front_shape) :=
  match children, ss with
  | [], [] => Some sh
  | j :: rest, s :: sorts =>
      if Nat.leb (S j) i then
        match front_require j s sh with
        | Some sh' => front_require_children i rest sorts sh'
        | None => None
        end
      else None
  | _, _ => None
  end.
TimeFun front_require_children.

Fixpoint front_require_nodes {V : Type} (tb : ptrie (list sort * output))
    (i : nat) (ns : list (pnode V)) (sh : list front_shape)
    : option (list front_shape) :=
  match ns with
  | [] => Some sh
  | n :: rest =>
      match n with
      | PApp f children =>
          match trie_get f tb with
          | Some (ss, OId) =>
              match front_require_children i children ss sh with
              | Some sh' => front_require_nodes tb (S i) rest sh'
              | None => None
              end
          | _ => None
          end
      | _ => front_require_nodes tb (S i) rest sh
      end
  end.
TimeFun front_require_nodes.

(** Each hole name is read once per occurrence, even when many edges use the same node. *)
Fixpoint front_holes {V : Type} (bind : bool) (ns : list (pnode V))
    (sh : list front_shape) (g : ptrie sort) : option (ptrie sort) :=
  match ns, sh with
  | [], [] => Some g
  | n :: rest, (Some s, true) :: shapes =>
      match n with
      | PHole h =>
          if bind then
            match @bind_b V g (Var h) s with
            | Some g' => front_holes bind rest shapes g'
            | None => None
            end
          else if @has_b V g (Var h) s then front_holes bind rest shapes g else None
      | PApp _ _ =>
          if sort_eqb s SId then front_holes bind rest shapes g else None
      | PLit _ =>
          if sort_eqb s SVal then front_holes bind rest shapes g else None
      end
  | _, _ => None
  end.
TimeFun front_holes.

Definition front_pattern {V : Type} (bind : bool) (tb : ptrie (list sort * output))
    (g : ptrie sort) (p : fpat V) : option (ptrie sort) :=
  match p with
  | FPat _ ns r =>
      if Nat.eqb (S r) (length ns) then
        match front_require r SId (map front_initial ns) with
        | None => None
        | Some sh =>
            match front_require_nodes tb 0 ns sh with
            | None => None
            | Some sh' => front_holes bind ns sh' g
            end
        end
      else None
  end.
TimeFun front_pattern.

Definition front_rewrite {V : Type} (tb : ptrie (list sort * output))
    (rw : rewrite V) : bool :=
  match rw with
  | Rewrite _ lhs_pat rhs_pat conditions =>
      match lhs_pat with
      | FPat _ ns r =>
          match nth_error ns r with
          | Some (PApp _ _) =>
              match front_pattern true tb Empty lhs_pat with
              | None => false
              | Some g0 =>
                  match bind_query_b tb g0 conditions with
                  | None => false
                  | Some g =>
                      match front_pattern false tb g rhs_pat with
                      | Some _ => true
                      | None => false
                      end
                  end
              end
          | _ => false
          end
      end
  end.
TimeFun front_rewrite.

Definition front_analysis_action {V : Type} (tb : ptrie (list sort * output))
    (a : action V) : bool :=
  match a with
  | Put f _ _ =>
      match trie_get f tb with
      | Some (_, ORel) | Some (_, OLat _) => true
      | _ => false
      end
  | Let _ _ _ => true
  | _ => false
  end.
TimeFun front_analysis_action.

Definition front_analysis {V : Type} (tb : ptrie (list sort * output))
    (r : rule V) : bool :=
  match r with
  | Rule _ _ acts => check_rule tb r && forallb (front_analysis_action tb) acts
  end.
TimeFun front_analysis.

Fixpoint front_expr_children {V : Type} (ns : list (enode V)) (i : nat)
    (children : list nat) (ss : list sort) : bool :=
  match children, ss with
  | [], [] => true
  | j :: rest, s :: sorts =>
      Nat.leb (S j) i &&
      match nth_error ns j with
      | Some n =>
          sort_eqb (match n with EApp _ _ => SId | ELit _ => SVal end) s &&
            front_expr_children ns i rest sorts
      | None => false
      end
  | _, _ => false
  end.
TimeFun front_expr_children.

Fixpoint front_expr_nodes {V : Type} (tb : ptrie (list sort * output))
    (ns : list (enode V)) (i : nat) (rest : list (enode V)) : bool :=
  match rest with
  | [] => true
  | n :: tail =>
      match n with
      | EApp f children =>
          match trie_get f tb with
          | Some (ss, OId) =>
              front_expr_children ns i children ss && front_expr_nodes tb ns (S i) tail
          | _ => false
          end
      | ELit _ => front_expr_nodes tb ns (S i) tail
      end
  end.
TimeFun front_expr_nodes.

Definition front_expr {V : Type} (tb : ptrie (list sort * output)) (e : fexpr V) : bool :=
  match e with
  | FExpr _ ns r =>
      match nth_error ns r with
      | Some (EApp _ _) => front_expr_nodes tb ns 0 ns
      | _ => false
      end
  end.
TimeFun front_expr.

(** Failure positions are counted within their own input list. *)
Fixpoint front_first_bad {A : Type} (check : A -> bool) (xs : list A) : option nat :=
  match xs with
  | [] => None
  | x :: rest =>
      if check x then
        match front_first_bad check rest with
        | Some n => Some (S n)
        | None => None
        end
      else Some 0
  end.
TimeFun front_first_bad.

Definition front_check {V : Type} (ds : list decl) (rws : list (rewrite V))
    (ans : list (rule V)) (es : list (fexpr V)) : option reject :=
  let tb := decl_table ds in
  match front_first_bad (front_rewrite tb) rws with
  | Some n => Some (BadRewrite n)
  | None =>
      match front_first_bad (front_analysis tb) ans with
      | Some n => Some (BadAnalysis n)
      | None =>
          match front_first_bad (front_expr tb) es with
          | Some n => Some (BadInput n)
          | None => None
          end
      end
  end.
TimeFun front_check.


(** * Pattern constraints *)

(** A shape records only sort requirements already imposed on its node. *)
Definition front_shape_sat {V} (g : ctx) (ns : list (pnode V))
    (sh : list front_shape) : Prop :=
  Forall2 (fun n shape => match fst shape with
    | Some s => pnode_sort g n = Some s
    | None => True
    end) ns sh.

(** A used position has both a required sort and a reference mark. *)
Definition front_used (sh : list front_shape) (j : nat) : Prop :=
  exists s, nth_error sh j = Some (Some s, true).

(** A child index is referenced by some constructor in the node list. *)
Definition front_referenced {V} (ns : list (pnode V)) (j : nat) : Prop :=
  exists i f ch, nth_error ns i = Some (PApp f ch) /\ In j ch.

(** Constructor requirements for a suffix use its original node positions. *)
Definition front_nodes_ok {V} (ds : list decl) (g : ctx) (all : list (pnode V))
    (i : nat) (ns : list (pnode V)) : Prop :=
  forall j f ch, nth_error ns j = Some (PApp f ch) ->
    lookup_kind ds f = Some OId /\ exists ss, lookup_sorts ds f = Some ss /\
      Forall2 (fun k s => k < i + j /\ exists n,
        nth_error all k = Some n /\ pnode_sort g n = Some s) ch ss.

(** Initial shapes impose exactly the fixed sorts of applications and literals. *)
Lemma front_initial_sat : forall V g (ns : list (pnode V)),
  front_shape_sat g ns (map front_initial ns).
Proof.
  intros V g ns. unfold front_shape_sat. induction ns as [|n ns IH].
  - constructor.
  - cbn [map]. constructor; [|exact IH].
    destruct n; cbn [front_initial fst pnode_sort]; auto.
Qed.

(** No initial shape has been marked by a root or child reference. *)
Lemma front_initial_unused : forall V (ns : list (pnode V)) j,
  ~ front_used (map front_initial ns) j.
Proof.
  intros V ns. induction ns as [|n ns IH].
  - intros [|j] [s Hnth]; discriminate Hnth.
  - intros [|j] [s Hnth]; cbn [map nth_error] in Hnth.
    + unfold front_initial in Hnth. discriminate Hnth.
    + apply (IH j). exists s. exact Hnth.
Qed.

(** A successful position constraint preserves length and marks exactly its position. *)
Lemma front_require_layout : forall j s sh sh', front_require j s sh = Some sh' ->
  length sh' = length sh /\ forall k, front_used sh' k <-> k = j \/ front_used sh k.
Proof.
  induction j as [|j IH]; intros s [|[old used] sh] sh' Hreq;
    cbn [front_require] in Hreq; try discriminate.
  - destruct old as [t|].
    + destruct (sort_eqb t s) eqn:Hsort; [|discriminate].
      injection Hreq as <-. split; [reflexivity|]. intros [|k]; unfold front_used;
        cbn [nth_error]; split; intros H.
      * left. reflexivity.
      * exists s. reflexivity.
      * destruct H as [u Hu]. right. exists u. exact Hu.
      * destruct H as [Hbad|H]; [discriminate|exact H].
    + injection Hreq as <-. split; [reflexivity|]. intros [|k]; unfold front_used;
        cbn [nth_error]; split; intros H.
      * left. reflexivity.
      * exists s. reflexivity.
      * destruct H as [u Hu]. right. exists u. exact Hu.
      * destruct H as [Hbad|H]; [discriminate|exact H].
  - destruct (front_require j s sh) as [tail|] eqn:Htail; [|discriminate].
    injection Hreq as <-. destruct (IH s sh tail Htail) as [Hlen Hused].
    split; [cbn [length]; congruence|]. intros [|k].
    + unfold front_used. cbn [nth_error]. split; [tauto|]. intros [Hbad|H];
        [discriminate|exact H].
    + change (front_used tail k <-> S k = S j \/ front_used sh k).
      rewrite Hused. split; intros [H|H]; [left; congruence|right; exact H|left; congruence|
        right; exact H].
Qed.

(** Interpreting a successful constraint validates both its input shapes and its position. *)
Lemma front_require_sound : forall V j s sh sh', front_require j s sh = Some sh' ->
  forall g (ns : list (pnode V)), front_shape_sat g ns sh' ->
    front_shape_sat g ns sh /\ exists n,
      nth_error ns j = Some n /\ pnode_sort g n = Some s.
Proof.
  intros V j. induction j as [|j IH]; intros s [|[old used] sh] sh' Hreq g ns Hsat;
    cbn [front_require] in Hreq; try discriminate.
  - destruct old as [t|].
    + destruct (sort_eqb t s) eqn:Hsort; [|discriminate].
      apply sort_eqb_spec in Hsort. subst t. injection Hreq as <-.
      inversion Hsat as [|n shape rest shapes Hhead Htail]; subst.
      cbn [fst] in Hhead. split.
      * constructor; assumption.
      * exists n. split; [reflexivity|exact Hhead].
    + injection Hreq as <-. inversion Hsat as [|n shape rest shapes Hhead Htail]; subst.
      cbn [fst] in Hhead. split.
      * constructor; [exact I|exact Htail].
      * exists n. split; [reflexivity|exact Hhead].
  - destruct (front_require j s sh) as [tail|] eqn:Htail; [|discriminate].
    injection Hreq as <-. inversion Hsat as [|n shape rest shapes Hhead Hrest]; subst.
    destruct (IH s sh tail Htail g rest Hrest) as [Hsat' [m [Hnth Hsort]]].
    split.
    + constructor; assumption.
    + exists m. split; assumption.
Qed.

(** A position compatible with an interpretation can always be constrained. *)
Lemma front_require_complete : forall V j s sh g (ns : list (pnode V)),
  front_shape_sat g ns sh ->
  (exists n, nth_error ns j = Some n /\ pnode_sort g n = Some s) ->
  exists sh', front_require j s sh = Some sh' /\ front_shape_sat g ns sh'.
Proof.
  intros V j. induction j as [|j IH]; intros s sh g ns Hsat [n [Hnth Hsort]];
    inversion Hsat as [|head shape rest shapes Hhead Htail]; subst; try discriminate.
  - cbn [nth_error] in Hnth. injection Hnth as <-. destruct shape as [old used].
    exists ((Some s, true) :: shapes). split.
    + cbn [front_require]. destruct old as [t|]; [|reflexivity].
      cbn [fst] in Hhead. assert (t = s) by congruence. subst t.
      rewrite (proj2 (sort_eqb_spec s s) eq_refl). reflexivity.
    + constructor; assumption.
  - cbn [nth_error] in Hnth.
    destruct (IH s shapes g rest Htail (ex_intro _ n (conj Hnth Hsort)))
      as [sh' [Hreq Hsat']].
    exists (shape :: sh'). split.
    + destruct shape as [old used]. cbn [front_require]. rewrite Hreq. reflexivity.
    + constructor; assumption.
Qed.


(** * Pattern fold proofs *)

(** Child constraints preserve length and mark exactly the listed child positions. *)
Lemma front_require_children_layout : forall i ch ss sh sh',
  front_require_children i ch ss sh = Some sh' ->
  length sh' = length sh /\ forall k, front_used sh' k <-> In k ch \/ front_used sh k.
Proof.
  intros i ch. induction ch as [|j ch IH]; intros [|s ss] sh sh' Hrun;
    cbn [front_require_children] in Hrun; try discriminate.
  - injection Hrun as <-. split; [reflexivity|]. intro k. cbn [In]. tauto.
  - destruct (Nat.leb (S j) i) eqn:Hlt; [|discriminate].
    destruct (front_require j s sh) as [sh1|] eqn:Hrequire; [|discriminate].
    destruct (IH ss sh1 sh' Hrun) as [Hlen Hused].
    destruct (front_require_layout j s sh sh1 Hrequire) as [Hlen1 Hused1].
    split; [congruence|]. intro k. rewrite Hused, Hused1. cbn [In]. intuition congruence.
Qed.

(** Successful child constraints validate the earlier indices and their node sorts. *)
Lemma front_require_children_sound : forall V i ch ss sh sh',
  front_require_children i ch ss sh = Some sh' ->
  forall g (ns : list (pnode V)), front_shape_sat g ns sh' ->
    front_shape_sat g ns sh /\
    Forall2 (fun j s => j < i /\ exists n,
      nth_error ns j = Some n /\ pnode_sort g n = Some s) ch ss.
Proof.
  intros V i ch. induction ch as [|j ch IH]; intros [|s ss] sh sh' Hrun g ns Hsat;
    cbn [front_require_children] in Hrun; try discriminate.
  - injection Hrun as <-. split; [exact Hsat|constructor].
  - destruct (Nat.leb (S j) i) eqn:Hlt; [|discriminate].
    destruct (front_require j s sh) as [sh1|] eqn:Hrequire; [|discriminate].
    destruct (IH ss sh1 sh' Hrun g ns Hsat) as [Hsat1 Hrest].
    destruct (front_require_sound V j s sh sh1 Hrequire g ns Hsat1) as [Hsat0 Hsort].
    split; [exact Hsat0|]. constructor; [|exact Hrest].
    split; [apply Nat.leb_le in Hlt; lia|exact Hsort].
Qed.

(** Earlier children of the required sorts are accepted by the constraint traversal. *)
Lemma front_require_children_complete : forall V i ch ss sh g (ns : list (pnode V)),
  front_shape_sat g ns sh ->
  Forall2 (fun j s => j < i /\ exists n,
    nth_error ns j = Some n /\ pnode_sort g n = Some s) ch ss ->
  exists sh', front_require_children i ch ss sh = Some sh' /\ front_shape_sat g ns sh'.
Proof.
  intros V i ch ss sh g ns Hsat Hchildren. revert sh Hsat.
  induction Hchildren as [|j s ch ss Hhead Htail IH]; intros sh Hsat.
  - exists sh. split; [reflexivity|exact Hsat].
  - destruct Hhead as [Hlt Hsort].
    destruct (front_require_complete V j s sh g ns Hsat Hsort) as [sh1 [Hreq Hsat1]].
    destruct (IH sh1 Hsat1) as [sh' [Hrun Hsat']]. exists sh'. split; [|exact Hsat'].
    cbn [front_require_children].
    rewrite (proj2 (Nat.leb_le (S j) i) ltac:(lia)), Hreq. exact Hrun.
Qed.

(** References in a node list come from its first constructor or its suffix. *)
Lemma front_referenced_cons : forall V (n : pnode V) ns k,
  front_referenced (n :: ns) k <->
  (match n with PApp _ ch => In k ch | _ => False end) \/ front_referenced ns k.
Proof.
  intros V n ns k. split.
  - intros [i [f [ch [Hnth Hin]]]]. destruct i as [|i]; cbn [nth_error] in Hnth.
    + injection Hnth as Hnode. subst n. left. exact Hin.
    + right. exists i, f, ch. split; assumption.
  - intros [Hhead|[i [f [ch [Hnth Hin]]]]].
    + destruct n as [h|f ch|v]; try contradiction.
      exists 0, f, ch. split; [reflexivity|exact Hhead].
    + exists (S i), f, ch. split; assumption.
Qed.

(** Walking constructors adds exactly the child marks of the visited nodes. *)
Lemma front_require_nodes_layout : forall V tb i (ns : list (pnode V)) sh sh',
  front_require_nodes tb i ns sh = Some sh' ->
  length sh' = length sh /\
    forall k, front_used sh' k <-> front_referenced ns k \/ front_used sh k.
Proof.
  intros V tb i ns. revert i. induction ns as [|n ns IH]; intros i sh sh' Hrun;
    cbn [front_require_nodes] in Hrun.
  - injection Hrun as <-. split; [reflexivity|]. intro k. split; [tauto|].
    intros [[j [f [ch [Hbad _]]]]|Hused]; [destruct j; discriminate|exact Hused].
  - destruct n as [h|f ch|v].
    + destruct (IH (S i) sh sh' Hrun) as [Hlen Hused]. split; [exact Hlen|].
      intro k. rewrite front_referenced_cons. cbn. rewrite Hused. tauto.
    + destruct (trie_get f tb) as [[ss out]|]; [|discriminate].
      destruct out; try discriminate.
      destruct (front_require_children i ch ss sh) as [sh1|] eqn:Hchildren;
        [|discriminate].
      destruct (IH (S i) sh1 sh' Hrun) as [Hlen Hused].
      destruct (front_require_children_layout i ch ss sh sh1 Hchildren) as [Hlen1 Hused1].
      split; [congruence|]. intro k.
      rewrite Hused, Hused1, front_referenced_cons. cbn. tauto.
    + destruct (IH (S i) sh sh' Hrun) as [Hlen Hused]. split; [exact Hlen|].
      intro k. rewrite front_referenced_cons. cbn. rewrite Hused. tauto.
Qed.

(** Successful constructor constraints validate every visited constructor declaration. *)
Lemma front_require_nodes_sound : forall V ds i (ns : list (pnode V)) sh sh',
  front_require_nodes (decl_table ds) i ns sh = Some sh' ->
  forall g all, front_shape_sat g all sh' ->
    front_shape_sat g all sh /\ front_nodes_ok ds g all i ns.
Proof.
  intros V ds i ns. revert i. induction ns as [|n ns IH];
    intros i sh sh' Hrun g all Hsat; cbn [front_require_nodes] in Hrun.
  - injection Hrun as <-. split; [exact Hsat|]. intros j f ch Hbad.
    destruct j; discriminate Hbad.
  - destruct n as [h|f ch|v].
    + destruct (IH (S i) sh sh' Hrun g all Hsat) as [Hsat0 Hnodes].
      split; [exact Hsat0|]. intros [|j] f ch Hnth; [discriminate|].
      replace (i + S j) with (S i + j) by lia. apply Hnodes. exact Hnth.
    + destruct (trie_get f (decl_table ds)) as [[ss out]|] eqn:Hlookup;
        [|discriminate]. destruct out; try discriminate.
      destruct (front_require_children i ch ss sh) as [sh1|] eqn:Hchildren;
        [|discriminate].
      destruct (IH (S i) sh1 sh' Hrun g all Hsat) as [Hsat1 Hnodes].
      destruct (front_require_children_sound V i ch ss sh sh1 Hchildren g all Hsat1)
        as [Hsat0 Htyped].
      destruct (proj1 (decl_table_lookup ds f ss OId) Hlookup) as [Hss Hkind].
      split; [exact Hsat0|]. intros [|j] f' ch' Hnth.
      * cbn [nth_error] in Hnth. injection Hnth as <- <-.
        split; [exact Hkind|]. exists ss. split; [exact Hss|].
        rewrite Nat.add_0_r. exact Htyped.
      * replace (i + S j) with (S i + j) by lia. apply Hnodes. exact Hnth.
    + destruct (IH (S i) sh sh' Hrun g all Hsat) as [Hsat0 Hnodes].
      split; [exact Hsat0|]. intros [|j] f ch Hnth; [discriminate|].
      replace (i + S j) with (S i + j) by lia. apply Hnodes. exact Hnth.
Qed.

(** Well-sorted constructors are accepted while preserving an interpretation of the shapes. *)
Lemma front_require_nodes_complete : forall V ds i (ns : list (pnode V)) sh g all,
  front_shape_sat g all sh -> front_nodes_ok ds g all i ns ->
  exists sh', front_require_nodes (decl_table ds) i ns sh = Some sh' /\
    front_shape_sat g all sh'.
Proof.
  intros V ds i ns. revert i. induction ns as [|n ns IH]; intros i sh g all Hsat Hnodes.
  - exists sh. split; [reflexivity|exact Hsat].
  - assert (Htail : front_nodes_ok ds g all (S i) ns).
    {
      intros j f ch Hnth. replace (S i + j) with (i + S j) by lia.
      apply Hnodes. exact Hnth.
    }
    destruct n as [h|f ch|v].
    + apply (IH (S i) sh g all Hsat Htail).
    + destruct (Hnodes 0 f ch eq_refl) as [Hkind [ss [Hss Htyped]]].
      rewrite Nat.add_0_r in Htyped.
      destruct (front_require_children_complete V i ch ss sh g all Hsat Htyped)
        as [sh1 [Hchildren Hsat1]].
      destruct (IH (S i) sh1 g all Hsat1 Htail) as [sh' [Hrun Hsat']].
      exists sh'. split; [|exact Hsat']. cbn [front_require_nodes].
      rewrite (proj2 (decl_table_lookup ds f ss OId) (conj Hss Hkind)), Hchildren.
      exact Hrun.
    + apply (IH (S i) sh g all Hsat Htail).
Qed.


(** * Completed pattern shapes *)

(** Every final shape has a sort and is referenced by a root or constructor. *)
Definition front_ready (sh : list front_shape) : Prop :=
  Forall (fun shape => exists s, shape = (Some s, true)) sh.

(** A shape list is ready exactly when every position is marked with a sort. *)
Lemma front_ready_used : forall sh,
  front_ready sh <-> forall j, j < length sh -> front_used sh j.
Proof.
  induction sh as [|shape sh IH].
  - split.
    + intros _ j Hlt. cbn [length] in Hlt. lia.
    + intro. constructor.
  - split.
    + intro Hready. inversion Hready as [|shape' sh' [s Hshape] Htail]; subst.
      intros [|j] Hlt.
      * exists s. reflexivity.
      * apply (proj1 IH Htail j). cbn [length] in Hlt. lia.
    + intro Hused. destruct (Hused 0 ltac:(cbn [length]; lia)) as [s Hshape].
      cbn [nth_error] in Hshape. injection Hshape as Hshape. constructor.
      * exists s. exact Hshape.
      * apply (proj2 IH). intros j Hlt. apply (Hused (S j)). cbn [length]. lia.
Qed.

(** Shape interpretation keeps one shape for each input node. *)
Lemma front_shape_sat_length : forall V g (ns : list (pnode V)) sh,
  front_shape_sat g ns sh -> length sh = length ns.
Proof.
  intros V g ns sh Hsat. induction Hsat; cbn [length]; congruence.
Qed.

(** Every child in a well-sorted constructor is earlier than that constructor. *)
Lemma front_children_before : forall V i g (ns : list (pnode V)) ch ss,
  Forall2 (fun j s => j < i /\ exists n,
    nth_error ns j = Some n /\ pnode_sort g n = Some s) ch ss ->
  forall j, In j ch -> j < i.
Proof.
  intros V i g ns ch ss Htyped. induction Htyped as [|k s ch ss Hhead Htail IH];
    intros j Hin; cbn [In] in Hin; [contradiction|].
  destruct Hin as [<-|Hin]; [exact (proj1 Hhead)|apply IH; exact Hin].
Qed.

(** A reference in a well-sorted node list comes from a later constructor. *)
Lemma front_referenced_later : forall V ds g (ns : list (pnode V)) j,
  front_nodes_ok ds g ns 0 ns -> front_referenced ns j ->
  exists i f ch, j < i /\ nth_error ns i = Some (PApp f ch) /\ In j ch.
Proof.
  intros V ds g ns j Hnodes [i [f [ch [Hnth Hin]]]].
  destruct (Hnodes i f ch Hnth) as [_ [ss [_ Htyped]]].
  exists i, f, ch. split; [|split; assumption].
  eapply front_children_before; [exact Htyped|exact Hin].
Qed.

(** A well-sorted pattern is exactly a complete compatible set of computed constraints. *)
Lemma front_pattern_shapes : forall V ds (ns : list (pnode V)) r g,
  pat_ok (lookup_sorts ds) (lookup_kind ds) g (FPat V ns r) <->
  S r = length ns /\ exists sh sh',
    front_require r SId (map front_initial ns) = Some sh /\
    front_require_nodes (decl_table ds) 0 ns sh = Some sh' /\
    front_shape_sat g ns sh' /\ front_ready sh'.
Proof.
  intros V ds ns r g. split.
  - intros [Hlast [Hroot [Hcoverage Hnodes]]].
    destruct (front_require_complete V r SId (map front_initial ns) g ns
      (front_initial_sat V g ns) Hroot) as [sh [Hroot_run Hsat]].
    assert (Htyped : front_nodes_ok ds g ns 0 ns).
    { intros i f ch Hnth. apply Hnodes. exact Hnth. }
    destruct (front_require_nodes_complete V ds 0 ns sh g ns Hsat Htyped)
      as [sh' [Hnodes_run Hsat']].
    split; [exact Hlast|]. exists sh, sh'. split; [exact Hroot_run|].
    split; [exact Hnodes_run|]. split; [exact Hsat'|].
    apply front_ready_used. intros j Hlt.
    pose proof (front_shape_sat_length V g ns sh' Hsat') as Hlen.
    destruct (front_require_nodes_layout V (decl_table ds) 0 ns sh sh' Hnodes_run)
      as [_ Hnodes_used]. apply Hnodes_used.
    destruct (Nat.eq_dec j r) as [->|Hneq].
    + right. apply (proj2 (proj2 (front_require_layout r SId _ sh Hroot_run) r)).
      left. reflexivity.
    + left. assert (j < r) by (cbn [root nodes] in Hlast; lia).
      destruct (Hcoverage j H) as [i [f [ch [_ [Hnth Hin]]]]].
      exists i, f, ch. split; assumption.
  - intros [Hlast [sh [sh' [Hroot_run [Hnodes_run [Hsat' Hready]]]]]].
    destruct (front_require_nodes_sound V ds 0 ns sh sh' Hnodes_run g ns Hsat')
      as [Hsat Hnodes].
    destruct (front_require_sound V r SId _ sh Hroot_run g ns Hsat) as [_ Hroot].
    unfold pat_ok. cbn [root nodes]. split; [exact Hlast|]. split; [exact Hroot|].
    split.
    + intros j Hlt. apply (front_referenced_later V ds g ns j Hnodes).
      pose proof (front_shape_sat_length V g ns sh' Hsat') as Hlen.
      pose proof (proj1 (front_ready_used sh') Hready j ltac:(lia)) as Hused.
      destruct (front_require_nodes_layout V (decl_table ds) 0 ns sh sh' Hnodes_run)
        as [_ Hnodes_used]. apply Hnodes_used in Hused. destruct Hused as [Href|Hused];
        [exact Href|].
      apply (proj2 (front_require_layout r SId _ sh Hroot_run) j) in Hused.
      destruct Hused as [Heq|Hinitial]; [lia|].
      exfalso. apply (front_initial_unused V ns j). exact Hinitial.
    + intros i f ch Hnth. apply Hnodes. exact Hnth.
Qed.


(** * Pattern hole contexts *)

(** Binding one hole preserves old bindings and adds exactly its required sort. *)
Lemma front_bind_var : forall V tr h s tr',
  @bind_b V tr (Var h) s = Some tr' ->
  trie_get h tr' = Some s /\
  (forall x u, trie_get x tr' = Some u <->
    trie_get x tr = Some u \/ (x = h /\ u = s)).
Proof.
  intros V tr h s tr' Hrun. cbn [bind_b] in Hrun.
  destruct (trie_get h tr) as [t|] eqn:Hlookup.
  - destruct (sort_eqb t s) eqn:Hsort; [|discriminate].
    apply sort_eqb_spec in Hsort. subst t. injection Hrun as <-.
    split; [exact Hlookup|]. intros x u. split; [intro H; left; exact H|].
    intros [H|[-> ->]]; assumption.
  - injection Hrun as <-. split; [apply PTrie.get_set_same|].
    intros x u. destruct (Pos.eq_dec x h) as [->|Hneq].
    + rewrite PTrie.get_set_same, Hlookup. split.
      * intro H. injection H as <-. right. split; reflexivity.
      * intros [H|[_ ->]]; [discriminate|reflexivity].
    + rewrite PTrie.get_set_other by exact Hneq. split.
      * intro H. left. exact H.
      * intros [H|[Heq _]]; [exact H|contradiction].
Qed.

(** A successful binding pass sorts every node and extends only the listed holes. *)
Lemma front_holes_bind_sound : forall V (ns : list (pnode V)) sh tr tr',
  front_holes true ns sh tr = Some tr' ->
  front_shape_sat (fun x => trie_get x tr') ns sh /\ front_ready sh /\
  (forall x s, trie_get x tr = Some s -> trie_get x tr' = Some s) /\
  (forall x s, trie_get x tr' = Some s ->
    trie_get x tr = Some s \/ In (PHole x) ns).
Proof.
  intros V ns. induction ns as [|n ns IH]; intros sh tr tr' Hrun.
  - destruct sh; cbn [front_holes] in Hrun; [|discriminate].
    injection Hrun as <-. split; [constructor|]. split; [constructor|].
    split; [intros; assumption|intros x s H; left; exact H].
  - destruct sh as [|[old used] sh]; [discriminate|].
    destruct old as [s|]; [|discriminate]. destruct used; [|discriminate].
    destruct n as [h|f ch|v]; cbn [front_holes] in Hrun.
    + destruct (bind_b tr (Var h) s) as [tr1|] eqn:Hbind; [|discriminate].
      destruct (front_bind_var V tr h s tr1 Hbind) as [Hhead Hbindings].
      destruct (IH sh tr1 tr' Hrun) as [Hsat [Hready [Hkeep Hscope]]].
      split.
      * constructor; [cbn [fst pnode_sort]; apply Hkeep; exact Hhead|exact Hsat].
      * split; [constructor; [exists s; reflexivity|exact Hready]|]. split.
        -- intros x u H. apply Hkeep. apply Hbindings. left. exact H.
        -- intros x u H. destruct (Hscope x u H) as [Hbound|Hin].
           ++ apply Hbindings in Hbound. destruct Hbound as [Hold|[-> _]].
              ** left. exact Hold.
              ** right. left. reflexivity.
           ++ right. right. exact Hin.
    + destruct (sort_eqb s SId) eqn:Hsort; [|discriminate].
      apply sort_eqb_spec in Hsort. subst s.
      destruct (IH sh tr tr' Hrun) as [Hsat [Hready [Hkeep Hscope]]].
      split; [constructor; [reflexivity|exact Hsat]|].
      split; [constructor; [exists SId; reflexivity|exact Hready]|].
      split; [exact Hkeep|]. intros x s H. destruct (Hscope x s H) as [Hold|Hin].
      * left. exact Hold.
      * right. right. exact Hin.
    + destruct (sort_eqb s SVal) eqn:Hsort; [|discriminate].
      apply sort_eqb_spec in Hsort. subst s.
      destruct (IH sh tr tr' Hrun) as [Hsat [Hready [Hkeep Hscope]]].
      split; [constructor; [reflexivity|exact Hsat]|].
      split; [constructor; [exists SVal; reflexivity|exact Hready]|].
      split; [exact Hkeep|]. intros x s H. destruct (Hscope x s H) as [Hold|Hin].
      * left. exact Hold.
      * right. right. exact Hin.
Qed.

(** A checking pass preserves its context and is also a successful binding pass. *)
Lemma front_holes_check_bind : forall V (ns : list (pnode V)) sh tr tr',
  front_holes false ns sh tr = Some tr' ->
  tr' = tr /\ front_holes true ns sh tr = Some tr.
Proof.
  intros V ns. induction ns as [|n ns IH]; intros sh tr tr' Hrun.
  - destruct sh; cbn [front_holes] in Hrun; [|discriminate].
    injection Hrun as <-. split; reflexivity.
  - destruct sh as [|[old used] sh]; [discriminate|].
    destruct old as [s|]; [|discriminate]. destruct used; [|discriminate].
    destruct n as [h|f ch|v]; cbn [front_holes] in Hrun |- *.
    + destruct (has_b tr (Var h) s) eqn:Hhas; [|discriminate].
      destruct (IH sh tr tr' Hrun) as [-> Htail]. split; [reflexivity|].
      apply (has_b_spec V tr (fun x => trie_get x tr) (Var h) s) in Hhas;
        [|intro; reflexivity].
      cbn [has] in Hhas. cbn [bind_b]. rewrite Hhas.
      rewrite (proj2 (sort_eqb_spec s s) eq_refl). exact Htail.
    + destruct (sort_eqb s SId) eqn:Hsort; [|discriminate].
      destruct (IH sh tr tr' Hrun) as [-> Htail]. split; [reflexivity|].
      exact Htail.
    + destruct (sort_eqb s SVal) eqn:Hsort; [|discriminate].
      destruct (IH sh tr tr' Hrun) as [-> Htail]. split; [reflexivity|].
      exact Htail.
Qed.

(** A ready shape list whose sorts agree with the context passes without changing it. *)
Lemma front_holes_check_complete : forall V (ns : list (pnode V)) sh tr g,
  (forall x, trie_get x tr = g x) ->
  front_shape_sat g ns sh -> front_ready sh ->
  front_holes false ns sh tr = Some tr.
Proof.
  intros V ns sh tr g Hrep Hsat. revert tr Hrep.
  induction Hsat as [|n shape ns sh Hhead Hsat IH]; intros tr Hrep Hready.
  - reflexivity.
  - inversion Hready as [|shape' sh' Hshape Hready']; subst.
    destruct Hshape as [s ->]. cbn [fst] in Hhead.
    destruct n as [h|f ch|v]; cbn [front_holes].
    + rewrite (proj2 (has_b_spec V tr g (Var h) s Hrep) Hhead).
      apply IH; assumption.
    + cbn [pnode_sort] in Hhead. injection Hhead as <-.
      apply IH; assumption.
    + cbn [pnode_sort] in Hhead. injection Hhead as <-.
      apply IH; assumption.
Qed.

(** A compatible partial context can accept one required hole binding. *)
Lemma front_bind_var_complete : forall V tr g h s,
  (forall x u, trie_get x tr = Some u -> g x = Some u) -> g h = Some s ->
  exists tr', @bind_b V tr (Var h) s = Some tr' /\
    (forall x u, trie_get x tr' = Some u -> g x = Some u).
Proof.
  intros V tr g h s Hpart Hhead. destruct (trie_get h tr) as [t|] eqn:Hlookup.
  - pose proof (Hpart h t Hlookup) as Hsort. assert (t = s) by congruence. subst t.
    exists tr. split; [|exact Hpart]. cbn [bind_b]. rewrite Hlookup.
    rewrite (proj2 (sort_eqb_spec s s) eq_refl). reflexivity.
  - exists (PTrieCode.set h s tr).
    assert (Hrun : @bind_b V tr (Var h) s = Some (PTrieCode.set h s tr)).
    { cbn [bind_b]. rewrite Hlookup. reflexivity. }
    split; [exact Hrun|]. intros x u Hnew.
    apply (proj2 (front_bind_var V tr h s _ Hrun) x u) in Hnew.
    destruct Hnew as [Hold|[-> ->]]; [apply Hpart; exact Hold|exact Hhead].
Qed.

(** Binding a ready, compatible shape list installs all of its holes. *)
Lemma front_holes_bind_complete : forall V (ns : list (pnode V)) sh tr g,
  (forall x u, trie_get x tr = Some u -> g x = Some u) ->
  front_shape_sat g ns sh -> front_ready sh ->
  exists tr', front_holes true ns sh tr = Some tr' /\
    (forall x u, trie_get x tr' = Some u -> g x = Some u) /\
    (forall h s, In (PHole h) ns -> g h = Some s -> trie_get h tr' = Some s).
Proof.
  intros V ns sh tr g Hpart Hsat. revert tr Hpart.
  induction Hsat as [|n shape ns sh Hhead Hsat IH]; intros tr Hpart Hready.
  - exists tr. split; [reflexivity|]. split; [exact Hpart|].
    intros h s Hin. contradiction.
  - inversion Hready as [|shape' sh' Hshape Hready']; subst.
    destruct Hshape as [s ->]. cbn [fst] in Hhead.
    destruct n as [h|f ch|v].
    + cbn [pnode_sort] in Hhead.
      destruct (front_bind_var_complete V tr g h s Hpart Hhead)
        as [tr1 [Hbind Hpart1]].
      destruct (IH tr1 Hpart1 Hready') as [tr' [Htail [Hpart' Hholes]]].
      exists tr'. split; [cbn [front_holes]; rewrite Hbind; exact Htail|].
      split; [exact Hpart'|]. intros x u [Heq|Hin] Hsort.
      * injection Heq as <-. assert (u = s) by congruence. subst u.
        destruct (front_holes_bind_sound V ns sh tr1 tr' Htail)
          as [_ [_ [Hkeep _]]].
        apply Hkeep. exact (proj1 (front_bind_var V tr h s tr1 Hbind)).
      * apply Hholes; assumption.
    + cbn [pnode_sort] in Hhead. injection Hhead as <-.
      destruct (IH tr Hpart Hready') as [tr' [Htail [Hpart' Hholes]]].
      exists tr'. split; [exact Htail|]. split; [exact Hpart'|].
      intros x u [Heq|Hin] Hsort; [discriminate|]. apply Hholes; assumption.
    + cbn [pnode_sort] in Hhead. injection Hhead as <-.
      destruct (IH tr Hpart Hready') as [tr' [Htail [Hpart' Hholes]]].
      exists tr'. split; [exact Htail|]. split; [exact Hpart'|].
      intros x u [Heq|Hin] Hsort; [discriminate|]. apply Hholes; assumption.
Qed.


(** * Pattern and rewrite reflection *)

(** Pointwise context agreement preserves the interpretation of each shape. *)
Lemma front_shape_sat_agrees : forall V g g' (ns : list (pnode V)) sh,
  (forall x, g x = g' x) -> front_shape_sat g ns sh -> front_shape_sat g' ns sh.
Proof.
  intros V g g' ns sh Hagree Hsat. induction Hsat as [|n shape ns sh Hhead Hsat IH].
  - constructor.
  - constructor; [|exact IH]. destruct shape as [[s|] used]; cbn [fst] in *;
      [|exact I].
    destruct n as [h|f ch|v]; cbn [pnode_sort] in *; [rewrite <- Hagree| |];
      exact Hhead.
Qed.

(** Binding a pattern from an empty context infers precisely its scoped hole sorts. *)
Lemma front_pattern_bind_sound : forall V ds (p : fpat V) tr,
  front_pattern true (decl_table ds) Empty p = Some tr ->
  pat_ok (lookup_sorts ds) (lookup_kind ds) (fun x => trie_get x tr) p /\
  (forall h s, trie_get h tr = Some s -> In (PHole h) (nodes V p)).
Proof.
  intros V ds [ns r] tr Hrun. cbn [front_pattern] in Hrun.
  destruct (Nat.eqb (S r) (length ns)) eqn:Hlast; [|discriminate].
  apply Nat.eqb_eq in Hlast.
  destruct (front_require r SId (map front_initial ns)) as [sh|] eqn:Hroot;
    [|discriminate].
  destruct (front_require_nodes (decl_table ds) 0 ns sh) as [sh'|] eqn:Hnodes;
    [|discriminate].
  destruct (front_holes_bind_sound V ns sh' Empty tr Hrun)
    as [Hsat [Hready [_ Hscope]]]. split.
  - apply front_pattern_shapes. split; [exact Hlast|]. exists sh, sh'.
    split; [exact Hroot|]. split; [exact Hnodes|]. split; assumption.
  - intros h s Hbound. destruct (Hscope h s Hbound) as [Hold|Hin]; [|exact Hin].
    rewrite PTrie.get_empty in Hold. discriminate.
Qed.

(** Every scoped pattern context is inferred by the binding pass. *)
Lemma front_pattern_bind_complete : forall V ds (p : fpat V) g,
  pat_ok (lookup_sorts ds) (lookup_kind ds) g p ->
  (forall h s, g h = Some s -> In (PHole h) (nodes V p)) ->
  exists tr, front_pattern true (decl_table ds) Empty p = Some tr /\
    (forall x, trie_get x tr = g x).
Proof.
  intros V ds [ns r] g Hpat Hscope.
  apply front_pattern_shapes in Hpat.
  destruct Hpat as [Hlast [sh [sh' [Hroot [Hnodes [Hsat Hready]]]]]].
  assert (Hempty : forall x u, trie_get x (@Empty sort) = Some u -> g x = Some u).
  { intros x u H. rewrite PTrie.get_empty in H. discriminate. }
  destruct (front_holes_bind_complete V ns sh' Empty g Hempty Hsat Hready)
    as [tr [Hholes [Hpart Hbound]]]. exists tr. split.
  - cbn [front_pattern]. apply Nat.eqb_eq in Hlast. rewrite Hlast, Hroot, Hnodes.
    exact Hholes.
  - intro x. destruct (g x) as [s|] eqn:Hget.
    + apply Hbound; [apply Hscope with s|]; exact Hget.
    + destruct (trie_get x tr) as [s|] eqn:Hlookup; [|reflexivity].
      pose proof (Hpart x s Hlookup) as Hsort. congruence.
Qed.

(** Checking a pattern accepts only shapes sorted in the supplied context. *)
Lemma front_pattern_check_sound : forall V ds (p : fpat V) tr tr' g,
  (forall x, trie_get x tr = g x) ->
  front_pattern false (decl_table ds) tr p = Some tr' ->
  pat_ok (lookup_sorts ds) (lookup_kind ds) g p.
Proof.
  intros V ds [ns r] tr tr' g Hrep Hrun. cbn [front_pattern] in Hrun.
  destruct (Nat.eqb (S r) (length ns)) eqn:Hlast; [|discriminate].
  apply Nat.eqb_eq in Hlast.
  destruct (front_require r SId (map front_initial ns)) as [sh|] eqn:Hroot;
    [|discriminate].
  destruct (front_require_nodes (decl_table ds) 0 ns sh) as [sh'|] eqn:Hnodes;
    [|discriminate].
  destruct (front_holes_check_bind V ns sh' tr tr' Hrun) as [_ Hbind].
  destruct (front_holes_bind_sound V ns sh' tr tr Hbind) as [Hsat [Hready _]].
  apply front_pattern_shapes. split; [exact Hlast|]. exists sh, sh'.
  split; [exact Hroot|]. split; [exact Hnodes|]. split; [|exact Hready].
  eapply front_shape_sat_agrees; [exact Hrep|exact Hsat].
Qed.

(** A sorted pattern passes the checking mode without altering its context. *)
Lemma front_pattern_check_complete : forall V ds (p : fpat V) tr g,
  (forall x, trie_get x tr = g x) ->
  pat_ok (lookup_sorts ds) (lookup_kind ds) g p ->
  front_pattern false (decl_table ds) tr p = Some tr.
Proof.
  intros V ds [ns r] tr g Hrep Hpat. apply front_pattern_shapes in Hpat.
  destruct Hpat as [Hlast [sh [sh' [Hroot [Hnodes [Hsat Hready]]]]]].
  cbn [front_pattern]. apply Nat.eqb_eq in Hlast. rewrite Hlast, Hroot, Hnodes.
  apply (front_holes_check_complete V ns sh' tr g); assumption.
Qed.

(** The executable rewrite check reflects the complete scoped sorting judgment. *)
Lemma front_rewrite_spec : forall V ds (rw : rewrite V),
  front_rewrite (decl_table ds) rw = true <->
  exists g, rewrite_ok (lookup_sorts ds) (lookup_kind ds) rw g.
Proof.
  intros V ds [[ns r] rhs_pat conditions]. split.
  - intro Hrun. cbn [front_rewrite] in Hrun.
    destruct (nth_error ns r) as [n|] eqn:Hroot; [|discriminate].
    destruct n as [h|f ch|v]; try discriminate.
    destruct (front_pattern true (decl_table ds) Empty (FPat V ns r))
      as [tr0|] eqn:Hleft; [|discriminate].
    destruct (bind_query_b (decl_table ds) tr0 conditions)
      as [tr|] eqn:Hquery; [|discriminate].
    destruct (front_pattern false (decl_table ds) tr rhs_pat)
      as [tr'|] eqn:Hright; [|discriminate].
    destruct (front_pattern_bind_sound V ds (FPat V ns r) tr0 Hleft)
      as [Hleft_sorted Hscope].
    destruct (bind_query_b_sound V ds conditions tr0 (fun x => trie_get x tr0) tr
      ltac:(intro; reflexivity) Hquery) as [g [Htyped Hrep]].
    pose proof (front_pattern_check_sound V ds rhs_pat tr tr' g Hrep Hright)
      as Hright_sorted.
    exists g. exists (fun x => trie_get x tr0). cbn [lhs rhs cond].
    split; [exists f, ch; exact Hroot|]. split; [exact Hleft_sorted|].
    split; [exact Hscope|]. split; assumption.
  - intros [g [g0 [Hroot [Hleft [Hscope [Hquery Hright]]]]]].
    cbn [lhs rhs cond] in Hroot, Hleft, Hscope, Hquery, Hright.
    destruct (front_pattern_bind_complete V ds (FPat V ns r) g0 Hleft Hscope)
      as [tr0 [Hleft_run Hrep0]].
    destruct (bind_query_b_complete V ds tr0 g0 conditions g Hrep0 Hquery)
      as [tr [Hquery_run Hrep]].
    pose proof (front_pattern_check_complete V ds rhs_pat tr g Hrep Hright)
      as Hright_run.
    destruct Hroot as [f [ch Hroot]]. cbn [nodes root] in Hroot.
    cbn [front_rewrite]. rewrite Hroot, Hleft_run, Hquery_run, Hright_run.
    reflexivity.
Qed.


(** * Front checker costs *)

(** Trie insertion pays only for the bits of its key. *)
Lemma front_set_clock : forall A x (a : A) tr,
  (PTrieCode.T_set x a tr <= 9 * N.of_nat (Pos.size_nat x + 1))%N.
Proof.
  intros A x a tr. pose proof (PTrieT.replace_clock_bound A x (Some a) tr).
  time_step.
Qed.

(** Each term contributes at least one unit of text. *)
Lemma front_term_positive : forall V (t : term V), 1 <= term_bits t.
Proof.
  intros V [x|v]; cbn [term_bits]; lia.
Qed.

(** Reading a term's sort pays for the bits of its variable name. *)
Lemma front_has_clock : forall V g (t : term V) s,
  (T_has_b g t s <= 8 * N.of_nat (term_bits t))%N.
Proof.
  intros V g [x|v] s; time_step;
    unfold T_sort_eqb; time_cbn; rewrite ?PTrieT.trie_get_clock; time_cases; nia.
Qed.

(** Binding a term's sort pays for its key lookup and possible insertion. *)
Lemma front_bind_clock : forall V g (t : term V) s,
  (T_bind_b g t s <= 16 * N.of_nat (term_bits t))%N.
Proof.
  intros V g [x|v] s; time_step;
    unfold T_sort_eqb; time_cbn; rewrite ?PTrieT.trie_get_clock;
    try pose proof (front_set_clock sort x s g); time_cases; nia.
Qed.

(** Argument checking visits each argument once. *)
Lemma front_has_list_clock : forall V (ts : list (term V)) ss g,
  (T_has_list_b g ts ss <= 16 * N.of_nat (terms_bits ts + 1))%N.
Proof.
  intros V ts. induction ts as [|t ts IH]; intros [|s ss] g; time_step.
  pose proof (front_has_clock V g t s). pose proof (IH ss g).
  pose proof (front_term_positive V t).
  unfold terms_bits in *. cbn [fold_right] in *. nia.
Qed.

(** Primitive argument checking visits each argument once. *)
Lemma front_has_vals_clock : forall V (ts : list (term V)) g,
  (T_has_vals_b g ts <= 16 * N.of_nat (terms_bits ts + 1))%N.
Proof.
  intros V ts. induction ts as [|t ts IH]; intro g; time_step.
  pose proof (front_has_clock V g t SVal). pose proof (IH g).
  pose proof (front_term_positive V t).
  unfold terms_bits in *. cbn [fold_right] in *. nia.
Qed.

(** Result checking visits at most one term. *)
Lemma front_has_result_clock : forall V g out (res : option (term V)),
  (T_has_result_b g out res <= 16 * N.of_nat (result_bits res + 1))%N.
Proof.
  intros V g out [t|]; destruct out; time_step;
    pose proof (front_has_clock V g t SId); pose proof (front_has_clock V g t SVal);
    unfold result_bits; nia.
Qed.

(** Argument binding visits each argument once. *)
Lemma front_bind_list_clock : forall V (ts : list (term V)) ss g,
  (T_bind_list_b g ts ss <= 32 * N.of_nat (terms_bits ts + 1))%N.
Proof.
  intros V ts. induction ts as [|t ts IH]; intros [|s ss] g; time_step.
  pose proof (front_bind_clock V g t s). pose proof (front_term_positive V t).
  destruct (bind_b g t s) as [g'|]; time_cbn.
  - pose proof (IH ss g'). unfold terms_bits in *. cbn [fold_right] in *. nia.
  - unfold terms_bits in *. cbn [fold_right] in *. nia.
Qed.

(** Result binding visits at most one term. *)
Lemma front_bind_result_clock : forall V g out (res : option (term V)),
  (T_bind_result_b g out res <= 32 * N.of_nat (result_bits res + 1))%N.
Proof.
  intros V g out [t|]; destruct out; time_step;
    pose proof (front_bind_clock V g t SId); pose proof (front_bind_clock V g t SVal);
    unfold result_bits; nia.
Qed.

(** Building the declaration table pays for each declaration key. *)
Lemma front_decls_clock : forall ds,
  (T_decl_table ds <= 16 * N.of_nat
    (S (fold_right (fun d n => (decl_bits d + n)%nat) 0%nat ds)))%N.
Proof.
  induction ds as [|d ds IH]; time_step.
  pose proof (front_set_clock (list sort * output)%type (name d) (arg_sorts d, out d)
    (decl_table ds)).
  unfold decl_bits in *. nia.
Qed.

(** Query checking pays for the text of each visited atom. *)
Lemma front_query_clock : forall V (q : list (atom V)) tb g,
  (T_bind_query_b tb g q <= 128 * N.of_nat
    (S (fold_right (fun a n => (atom_bits a + n)%nat) 0%nat q)))%N.
Proof.
  intros V q. induction q as [|a q IH]; intros tb g.
  - time_step.
  - destruct a as [f args res | op args res].
    + time_step. rewrite PTrieT.trie_get_clock.
      destruct (trie_get f tb) as [[ss out]|]; time_cbn; [|nia].
      destruct (reads_b ss out); time_cbn; [|nia].
      pose proof (front_bind_list_clock V args ss g).
      destruct (bind_list_b g args ss) as [g1|]; time_cbn; [|nia].
      pose proof (front_bind_result_clock V g1 out res).
      destruct (bind_result_b g1 out res) as [g2|]; time_cbn; [|nia].
      pose proof (IH tb g2). nia.
    + time_step. pose proof (front_has_vals_clock V args g).
      pose proof (front_has_clock V g res SVal). pose proof (IH tb g).
      time_cases; time_cbn; nia.
Qed.

(** Action checking pays for each action's variable and function keys. *)
Lemma front_actions_clock : forall V (acts : list (action V)) tb g,
  (T_check_actions_b tb g acts <= 128 * N.of_nat
    (S (fold_right (fun a n => (action_bits a + n)%nat) 0%nat acts)))%N.
Proof.
  intros V acts. induction acts as [|a acts IH]; intros tb g.
  - time_step.
  - destruct a as [x f args | f args res | t u | x op args].
    + time_step. rewrite PTrieT.trie_get_clock.
      destruct (trie_get f tb) as [[ss out]|]; time_cbn; [|nia].
      destruct out; time_cbn; try nia.
      pose proof (front_has_list_clock V args ss g).
      pose proof (front_set_clock sort x SId g).
      pose proof (IH tb (PTrieCode.set x SId g)). nia.
    + time_step. rewrite PTrieT.trie_get_clock.
      destruct (trie_get f tb) as [[ss out]|]; time_cbn; [|nia].
      pose proof (front_has_list_clock V args ss g).
      pose proof (front_has_result_clock V g out res). pose proof (IH tb g). nia.
    + time_step. pose proof (front_has_clock V g t SId).
      pose proof (front_has_clock V g u SId). pose proof (IH tb g). nia.
    + time_step. pose proof (front_has_vals_clock V args g).
      pose proof (front_set_clock sort x SVal g).
      pose proof (IH tb (PTrieCode.set x SVal g)). nia.
Qed.

(** Rule checking composes its query and action passes. *)
Lemma front_rule_clock : forall V (r : rule V) tb,
  (T_check_rule tb r <= 512 * N.of_nat (rule_bits r))%N.
Proof.
  intros V [q acts] tb. pose proof (front_query_clock V q tb Empty).
  time_step. destruct (bind_query_b tb Empty q) as [g|]; time_cbn; [|nia].
  pose proof (front_actions_clock V acts tb g). nia.
Qed.

(** A sum's initial offset is counted exactly once. *)
Lemma front_sum_offset : forall A (w : A -> nat) k xs,
  fold_right (fun a n => w a + n) k xs =
  fold_right (fun a n => w a + n) 0 xs + k.
Proof.
  intros A w k xs. induction xs as [|a xs IH]; cbn [fold_right]; lia.
Qed.

(** The pattern text pays at least once for each node. *)
Lemma front_pattern_length : forall V (ns : list (pnode V)),
  length ns <= fold_right (fun n m => pnode_size n + m) 0 ns.
Proof.
  intros V ns. induction ns as [|n ns IH]; cbn [length fold_right]; [lia|].
  destruct n; cbn [pnode_size]; lia.
Qed.

(** Updating a shape walks only the prefix named by its index. *)
Lemma front_require_clock : forall j s sh,
  (T_front_require j s sh <= 4 * N.of_nat (j + 1))%N.
Proof.
  induction j as [|j IH]; intros s [|[old used] sh]; time_step.
Qed.

(** Every constructor child pays for one bound check and one prefix update. *)
Lemma front_require_children_clock : forall i ch ss sh,
  (T_front_require_children i ch ss sh <= 16 * N.of_nat
    (fold_right (fun j n => (j + 1 + n)%nat) 0%nat ch + 1))%N.
Proof.
  intros i ch. induction ch as [|j ch IH]; intros [|s ss] sh;
    time_unfold @T_front_require_children; time_simpl; cbn [fold_right]; try lia.
  pose proof (Nat.T_leb_le (S j) i).
  pose proof (front_require_clock j s sh).
  destruct (Nat.leb (S j) i); time_simpl; [|nia].
  destruct (front_require j s sh) as [sh'|]; time_simpl; [|nia].
  pose proof (IH ss sh'). nia.
Qed.

(** The constructor pass pays for names and the written child indices. *)
Lemma front_require_nodes_clock : forall V tb i (ns : list (pnode V)) sh,
  (T_front_require_nodes tb i ns sh <= 32 * N.of_nat
    (fold_right (fun n m => (pnode_size n + m)%nat) 0%nat ns + 1))%N.
Proof.
  intros V tb i ns. revert i. induction ns as [|n ns IH]; intros i sh.
  - time_step.
  - destruct n as [h|f ch|v].
    + time_step.
    + time_step. rewrite PTrieT.trie_get_clock.
      destruct (trie_get f tb) as [[ss out]|]; time_cbn; [|nia].
      destruct out; time_cbn; try nia.
      pose proof (front_require_children_clock i ch ss sh).
      destruct (front_require_children i ch ss sh) as [sh'|]; time_cbn; [|nia].
      pose proof (IH (S i) sh'). nia.
    + time_step.
Qed.

(** The hole pass pays for each hole key or fixed node sort once. *)
Lemma front_holes_clock : forall V bind (ns : list (pnode V)) sh g,
  (T_front_holes bind ns sh g <= 64 * N.of_nat
    (fold_right (fun n m => (pnode_size n + m)%nat) 0%nat ns + 1))%N.
Proof.
  intros V bind ns. induction ns as [|n ns IH]; intros sh g.
  - time_step.
  - destruct sh as [|[old used] sh]; [time_step|].
    destruct old as [s|]; [|time_step]. destruct used; [|time_step].
    destruct n as [h|f ch|v].
    + destruct bind.
      * time_unfold @T_front_holes; time_simpl; cbn [fold_right pnode_size].
        pose proof (front_bind_clock V g (Var h) s) as Hbind.
        cbn [term_bits] in Hbind.
        destruct (@bind_b V g (Var h) s) as [g'|]; time_simpl; [|nia].
        pose proof (IH sh g'). nia.
      * time_unfold @T_front_holes; time_simpl; cbn [fold_right pnode_size].
        pose proof (front_has_clock V g (Var h) s) as Hhas.
        cbn [term_bits] in Hhas. pose proof (IH sh g).
        destruct (@has_b V g (Var h) s); time_simpl; nia.
    + time_unfold @T_front_holes; time_simpl; cbn [fold_right pnode_size].
      pose proof (IH sh g). destruct (sort_eqb s SId); time_simpl; nia.
    + time_unfold @T_front_holes; time_simpl; cbn [fold_right pnode_size].
      pose proof (IH sh g). destruct (sort_eqb s SVal); time_simpl; nia.
Qed.

(** Initializing one shape per node is linear in the number of nodes. *)
Lemma front_initial_clock : forall V (ns : list (pnode V)),
  (ListDef.T_map front_initial (fun n => T_front_initial n) ns <=
    3 * N.of_nat (length ns + 1))%N.
Proof.
  intros V ns.
  pose proof (ListDef.T_map_le (@front_initial V) (fun n => T_front_initial n)
    1%N ns ltac:(intro n; unfold T_front_initial; lia)). nia.
Qed.

(** Pattern checking pays for its node text, root and child indices. *)
Lemma front_pattern_clock : forall V bind tb g (p : fpat V),
  (T_front_pattern bind tb g p <= 128 * N.of_nat (pat_size p + 1))%N.
Proof.
  intros V bind tb g [ns r].
  pose proof (front_pattern_length V ns).
  pose proof (front_initial_clock V ns) as Hinitial.
  unfold T_front_initial in Hinitial.
  pose proof (front_require_clock r SId (map front_initial ns)).
  time_unfold @T_front_pattern; time_simpl.
  unfold pat_size. cbn [nodes root]. rewrite front_sum_offset.
  pose proof (Datatypes.T_length_le ns).
  pose proof (Nat.T_eqb_le (S r) (length ns)).
  destruct (Nat.eqb (S r) (length ns)); time_simpl; [|nia].
  destruct (front_require r SId (map front_initial ns)) as [sh|]; time_simpl; [|nia].
  pose proof (front_require_nodes_clock V tb 0 ns sh).
  destruct (front_require_nodes tb 0 ns sh) as [sh'|]; time_simpl; [|nia].
  pose proof (front_holes_clock V bind ns sh' g). nia.
Qed.

(** Rewrite checking pays for both patterns and the condition text. *)
Lemma front_rewrite_clock : forall V tb (rw : rewrite V),
  (T_front_rewrite tb rw <= 512 * N.of_nat (rewrite_size rw + 1))%N.
Proof.
  intros V tb [[ns r] rhs_pat conditions].
  pose proof (front_pattern_clock V true tb Empty (FPat V ns r)).
  assert (Hroot : r + 1 <= pat_size (FPat V ns r)).
  { unfold pat_size. cbn [nodes root]. rewrite front_sum_offset. lia. }
  time_unfold @T_front_rewrite; time_simpl.
  unfold rewrite_size. cbn [lhs rhs cond].
  pose proof (List.T_nth_error_le ns r).
  destruct (nth_error ns r) as [n|]; time_simpl; [|nia].
  destruct n as [h|f ch|v]; time_simpl; try nia.
  destruct (front_pattern true tb Empty (FPat V ns r)) as [g0|]; time_simpl; [|nia].
  pose proof (front_query_clock V conditions tb g0).
  destruct (bind_query_b tb g0 conditions) as [g|]; time_simpl; [|nia].
  pose proof (front_pattern_clock V false tb g rhs_pat). nia.
Qed.

(** Each action contributes at least one unit of text. *)
Lemma front_action_positive : forall V (a : action V), 1 <= action_bits a.
Proof.
  intros V a. destruct a; cbn [action_bits]; lia.
Qed.

(** Checking an analysis action reads at most its function name. *)
Lemma front_analysis_action_clock : forall V tb (a : action V),
  (T_front_analysis_action tb a <= 8 * N.of_nat (action_bits a))%N.
Proof.
  intros V tb a. destruct a; time_step; rewrite ?PTrieT.trie_get_clock; nia.
Qed.

(** The analysis restriction pass visits each action once. *)
Lemma front_analysis_actions_clock : forall V tb (acts : list (action V)),
  (List.T_forallb (front_analysis_action tb) (fun a => T_front_analysis_action tb a)
    acts <= 16 * N.of_nat
      (fold_right (fun a n => (action_bits a + n)%nat) 0%nat acts + 1))%N.
Proof.
  intros V tb acts. induction acts as [|a acts IH].
  - time_step.
  - time_unfold @List.T_forallb; time_simpl; cbn [fold_right].
    pose proof (front_analysis_action_clock V tb a).
    pose proof (front_action_positive V a). nia.
Qed.

(** Analysis checking composes ordinary typing with the allowed-action pass. *)
Lemma front_analysis_clock : forall V tb (r : rule V),
  (T_front_analysis tb r <= 1024 * N.of_nat (rule_bits r))%N.
Proof.
  intros V tb [q acts].
  pose proof (front_rule_clock V (Rule V q acts) tb).
  pose proof (front_analysis_actions_clock V tb acts).
  time_unfold @T_front_analysis; time_simpl.
  unfold rule_bits in *. cbn [query actions] in *. nia.
Qed.

(** Expression child checking pays for its bound and prefix lookup. *)
Lemma front_expr_children_clock : forall V (ns : list (enode V)) i ch ss,
  (T_front_expr_children ns i ch ss <= 16 * N.of_nat
    (fold_right (fun j n => (j + 1 + n)%nat) 0%nat ch + 1))%N.
Proof.
  intros V ns i ch. induction ch as [|j ch IH]; intros [|s ss];
    time_unfold @T_front_expr_children; time_simpl; cbn [fold_right]; try lia.
  pose proof (Nat.T_leb_le (S j) i).
  pose proof (List.T_nth_error_le ns j).
  pose proof (IH ss).
  destruct (nth_error ns j) as [n|]; time_simpl; [|nia].
  destruct n; time_simpl; nia.
Qed.

(** Expression node checking reads each constructor name and its child indices. *)
Lemma front_expr_nodes_clock : forall V tb (ns : list (enode V)) i rest,
  (T_front_expr_nodes tb ns i rest <= 32 * N.of_nat
    (fold_right (fun n m => (enode_size n + m)%nat) 0%nat rest + 1))%N.
Proof.
  intros V tb ns i rest. revert i. induction rest as [|n rest IH]; intro i.
  - time_step.
  - destruct n as [f ch|v].
    + time_unfold @T_front_expr_nodes; time_simpl; cbn [fold_right enode_size].
      rewrite PTrieT.trie_get_clock.
      destruct (trie_get f tb) as [[ss out]|]; time_simpl; [|nia].
      destruct out; time_simpl; try nia.
      pose proof (front_expr_children_clock V ns i ch ss).
      pose proof (IH (S i)). nia.
    + time_step.
Qed.

(** Expression checking includes its root lookup in the input-size budget. *)
Lemma front_expr_clock : forall V tb (e : fexpr V),
  (T_front_expr tb e <= 64 * N.of_nat (expr_size e + 1))%N.
Proof.
  intros V tb [ns r]. time_unfold @T_front_expr; time_simpl.
  unfold expr_size. cbn [expr_nodes expr_root]. rewrite front_sum_offset.
  pose proof (List.T_nth_error_le ns r).
  destruct (nth_error ns r) as [n|]; time_simpl; [|nia].
  destruct n as [f ch|v]; time_simpl; [|nia].
  pose proof (front_expr_nodes_clock V tb ns 0 ns). nia.
Qed.

(** The root and both pattern headers make rewrite size positive. *)
Lemma front_rewrite_positive : forall V (rw : rewrite V), 1 <= rewrite_size rw.
Proof.
  intros V [[ln lr] [rn rr] conditions]. unfold rewrite_size, pat_size.
  cbn [lhs rhs cond nodes root].
  rewrite (front_sum_offset (pnode V) pnode_size (lr + 1) ln),
    (front_sum_offset (pnode V) pnode_size (rr + 1) rn). lia.
Qed.

(** Every expression includes its root index. *)
Lemma front_expr_positive : forall V (e : fexpr V), 1 <= expr_size e.
Proof.
  intros V [ns r]. unfold expr_size. cbn [expr_nodes expr_root].
  rewrite front_sum_offset. lia.
Qed.

(** First-error traversal adds bounded overhead to the checks it visits. *)
Lemma front_first_bad_clock : forall A (check : A -> bool) (T_check : A -> N)
    (weight : A -> nat) k xs,
  (forall x, 1 <= weight x) ->
  (forall x, (T_check x <= k * N.of_nat (weight x))%N) ->
  (T_front_first_bad check T_check xs <= (k + 4) * N.of_nat
    (fold_right (fun x n => (weight x + n)%nat) 0%nat xs + 1))%N.
Proof.
  intros A check T_check weight k xs Hpositive Hcheck.
  induction xs as [|x xs IH]; time_unfold @T_front_first_bad; time_simpl;
    cbn [fold_right]; [nia|].
  pose proof (Hpositive x). pose proof (Hcheck x).
  destruct (check x); time_simpl; [|nia].
  destruct (front_first_bad check xs); time_simpl; nia.
Qed.

(** The whole front-end checker is linear in the declared input text measure. *)
Lemma front_check_clock : forall V ds (rws : list (rewrite V)) ans es,
  (T_front_check ds rws ans es <= 4096 * N.of_nat (front_size ds rws ans es + 1))%N.
Proof.
  intros V ds rws ans es.
  pose proof (front_decls_clock ds) as Hdecls.
  assert (Hrewrite : forall rw : rewrite V,
    (T_front_rewrite (decl_table ds) rw <= 1024 * N.of_nat (rewrite_size rw))%N).
  { intro rw. pose proof (front_rewrite_clock V (decl_table ds) rw).
    pose proof (front_rewrite_positive V rw). nia. }
  pose proof (front_first_bad_clock (rewrite V) (front_rewrite (decl_table ds))
    (fun rw => T_front_rewrite (decl_table ds) rw) rewrite_size 1024%N rws
    (front_rewrite_positive V) Hrewrite) as Hrewrites.
  assert (Hrule_positive : forall r : rule V, 1 <= rule_bits r).
  { intro r. unfold rule_bits. lia. }
  pose proof (front_first_bad_clock (rule V) (front_analysis (decl_table ds))
    (fun r => T_front_analysis (decl_table ds) r) rule_bits 1024%N ans
    Hrule_positive (front_analysis_clock V (decl_table ds))) as Hanalyses.
  assert (Hexpr : forall e : fexpr V,
    (T_front_expr (decl_table ds) e <= 128 * N.of_nat (expr_size e))%N).
  { intro e. pose proof (front_expr_clock V (decl_table ds) e).
    pose proof (front_expr_positive V e). nia. }
  pose proof (front_first_bad_clock (fexpr V) (front_expr (decl_table ds))
    (fun e => T_front_expr (decl_table ds) e) expr_size 128%N es
    (front_expr_positive V) Hexpr) as Hexprs.
  time_unfold @T_front_check; time_simpl. unfold front_size.
  destruct (front_first_bad (front_rewrite (decl_table ds)) rws); time_simpl; [nia|].
  destruct (front_first_bad (front_analysis (decl_table ds)) ans); time_simpl; [nia|].
  destruct (front_first_bad (front_expr (decl_table ds)) es); time_simpl; nia.
Qed.


(** The first-error traversal succeeds exactly when every item passes. *)
Lemma front_first_bad_none : forall A (check : A -> bool) xs,
  front_first_bad check xs = None <-> Forall (fun x => check x = true) xs.
Proof.
  intros A check xs. induction xs as [|x xs IH]; cbn [front_first_bad].
  - split; [intro; constructor|intro; reflexivity].
  - destruct (check x) eqn:Hx.
    + destruct (front_first_bad check xs) as [n|] eqn:Hrest.
      * split; [discriminate|intro H].
        inversion H as [|x' xs' Hhead Htail]; subst.
        apply IH in Htail. discriminate.
      * split.
        -- intro. constructor; [exact Hx|apply IH; reflexivity].
        -- intro. reflexivity.
    + split; [discriminate|intro H; inversion H; congruence].
Qed.

(** A reported position names an actual item that failed its Boolean check. *)
Lemma front_first_bad_some : forall A (check : A -> bool) xs n,
  front_first_bad check xs = Some n ->
  exists x, nth_error xs n = Some x /\ check x = false.
Proof.
  intros A check xs. induction xs as [|x xs IH]; intros n Hbad;
    cbn [front_first_bad] in Hbad; [discriminate|].
  destruct (check x) eqn:Hx.
  - destruct (front_first_bad check xs) as [j|] eqn:Hrest; [|discriminate].
    injection Hbad as <-. destruct (IH j eq_refl) as [y [Hnth Hy]].
    exists y. split; assumption.
  - injection Hbad as <-. exists x. split; [reflexivity|exact Hx].
Qed.

(** Child checks enforce earlier indices and the declared sorts at those positions. *)
Lemma front_expr_children_spec : forall V (ns : list (enode V)) i ch ss,
  front_expr_children ns i ch ss = true <->
  Forall2 (fun j s => j < i /\ exists n,
    nth_error ns j = Some n /\ enode_sort n = s) ch ss.
Proof.
  intros V ns i ch. induction ch as [|j ch IH]; intros [|s ss];
    cbn [front_expr_children].
  - split; [intro; constructor|intro; reflexivity].
  - split; [discriminate|intro H; inversion H].
  - split; [discriminate|intro H; inversion H].
  - rewrite andb_true_iff. destruct (nth_error ns j) as [n|] eqn:Hnth.
    + change ((Nat.leb (S j) i = true /\
        (sort_eqb (enode_sort n) s && front_expr_children ns i ch ss) = true) <->
        Forall2 (fun j s => j < i /\ exists n,
          nth_error ns j = Some n /\ enode_sort n = s) (j :: ch) (s :: ss)).
      rewrite andb_true_iff, sort_eqb_spec, IH, Nat.leb_le.
      split.
      * intros [Hlt [Hsort Htail]]. constructor; [|exact Htail].
        split; [lia|]. exists n. split; assumption.
      * intro H. inversion H as [|j' s' ch' ss' Hhead Htail]; subst.
        destruct Hhead as [Hlt [m [Hm Hsort]]].
        assert (m = n) by congruence. subst m. repeat split; try assumption; lia.
    + split.
      * intros [_ Hfalse]. discriminate.
      * intro H. inversion H as [|j' s' ch' ss' Hhead Htail]; subst.
        destruct Hhead as [_ [n [Hbad _]]]. congruence.
Qed.

(** Declaration-table outputs have exactly the first-declaration lookup semantics. *)
Lemma front_table_kind : forall ds f,
  option_map snd (trie_get f (decl_table ds)) = lookup_kind ds f.
Proof.
  induction ds as [|d ds IH]; intro f; cbn [decl_table lookup_kind].
  - rewrite PTrie.get_empty. reflexivity.
  - destruct (Pos.eqb (name d) f) eqn:Hname.
    + apply Pos.eqb_eq in Hname. subst f. rewrite PTrie.get_set_same. reflexivity.
    + rewrite PTrie.get_set_other; [apply IH|].
      apply Pos.eqb_neq in Hname. congruence.
Qed.

(** Analysis actions create values or write declared relations and lattice functions. *)
Lemma front_analysis_action_spec : forall V ds (a : action V),
  front_analysis_action (decl_table ds) a = true <-> analysis_action (lookup_kind ds) a.
Proof.
  intros V ds [x f args|f args res|t u|x op args];
    cbn [front_analysis_action analysis_action].
  - split; [discriminate|contradiction].
  - pose proof (front_table_kind ds f) as Hkind.
    destruct (trie_get f (decl_table ds)) as [[ss out]|];
      cbn [option_map snd] in Hkind; rewrite <- Hkind.
    + destruct out.
      * split; [intro; now left|intro; reflexivity].
      * split; [discriminate|]. intros [Hbad|[m Hbad]]; discriminate.
      * split; [intro; right; eexists; reflexivity|intro; reflexivity].
    + split; [discriminate|]. intros [Hbad|[m Hbad]]; discriminate.
  - split; [discriminate|contradiction].
  - split; [intro; exact I|intro; reflexivity].
Qed.

(** A one-rule use of the reviewed checker reflects the rule's declarative judgment. *)
Lemma front_rule_spec : forall V ds (r : rule V),
  check_rule (decl_table ds) r = true <-> rule_ok (lookup_sorts ds) (lookup_kind ds) r.
Proof.
  intros V ds r.
  pose proof (check_program_spec V (Program V ds [r])) as Hprogram.
  cbn [check_program check_rules program_ok decls rules program_sorts program_kind]
    in Hprogram.
  rewrite andb_true_r in Hprogram.
  split.
  - intro Hcheck. apply Hprogram in Hcheck.
    inversion Hcheck as [|r' rs Hrule Hrest]; subst. exact Hrule.
  - intro Hrule. apply Hprogram. constructor; [exact Hrule|constructor].
Qed.

(** The analysis checker enforces both ordinary sorting and the restricted action forms. *)
Lemma front_analysis_spec : forall V ds (r : rule V),
  front_analysis (decl_table ds) r = true <-> analysis_ok (lookup_sorts ds) (lookup_kind ds) r.
Proof.
  intros V ds [q acts]. unfold front_analysis, analysis_ok.
  rewrite andb_true_iff, front_rule_spec. cbn [actions].
  assert (Hactions : forallb (front_analysis_action (decl_table ds)) acts = true <->
    Forall (analysis_action (lookup_kind ds)) acts).
  {
    rewrite forallb_forall, Forall_forall. split; intros H a Hin.
    - apply front_analysis_action_spec. exact (H a Hin).
    - apply front_analysis_action_spec. exact (H a Hin).
  }
  rewrite Hactions. tauto.
Qed.

(** A constructor at position [i] has its declared earlier children. *)
Definition front_expr_condition {V : Type} (ds : list decl) (ns : list (enode V))
    (i : nat) (f : positive) (children : list nat) : Prop :=
  lookup_kind ds f = Some OId /\ exists ss, lookup_sorts ds f = Some ss /\
    Forall2 (fun j s => j < i /\ exists n,
      nth_error ns j = Some n /\ enode_sort n = s) children ss.

(** Scanning a suffix checks its constructors at their positions in the whole expression. *)
Lemma front_expr_nodes_spec : forall V ds (ns rest : list (enode V)) start,
  front_expr_nodes (decl_table ds) ns start rest = true <->
  forall i f children, nth_error rest i = Some (EApp f children) ->
    front_expr_condition ds ns (start + i) f children.
Proof.
  intros V ds ns rest. induction rest as [|n rest IH]; intro start.
  - cbn [front_expr_nodes]. split; [|intro; reflexivity].
    intros _ i f ch Hnth. destruct i; discriminate.
  - destruct n as [f ch|v]; cbn [front_expr_nodes].
    + destruct (trie_get f (decl_table ds)) as [[ss out]|] eqn:Hlookup.
      * destruct (proj1 (decl_table_lookup ds f ss out) Hlookup) as [Hss Hout].
        destruct out.
        -- split; [discriminate|intro H].
           specialize (H 0 f ch eq_refl). unfold front_expr_condition in H.
           destruct H as [Hkind _]. congruence.
        -- rewrite andb_true_iff, front_expr_children_spec, IH.
           split.
           ++ intros [Hchildren Hrest] [|i] f' ch' Hnth.
              ** cbn [nth_error] in Hnth. injection Hnth as <- <-.
                 unfold front_expr_condition. rewrite Nat.add_0_r.
                 split; [exact Hout|]. exists ss. split; assumption.
              ** cbn [nth_error] in Hnth.
                 replace (start + S i) with (S start + i) by lia.
                 exact (Hrest i f' ch' Hnth).
           ++ intro H. split.
              ** specialize (H 0 f ch eq_refl). unfold front_expr_condition in H.
                 rewrite Nat.add_0_r in H.
                 destruct H as [_ [ss' [Hss' Hchildren]]].
                 assert (ss' = ss) by congruence. subst ss'. exact Hchildren.
              ** intros i f' ch' Hnth.
                 replace (S start + i) with (start + S i) by lia.
                 apply H. exact Hnth.
        -- split; [discriminate|intro H].
           specialize (H 0 f ch eq_refl). unfold front_expr_condition in H.
           destruct H as [Hkind _]. congruence.
      * split; [discriminate|intro H].
        specialize (H 0 f ch eq_refl). unfold front_expr_condition in H.
        destruct H as [Hout [ss [Hss _]]].
        pose proof (proj2 (decl_table_lookup ds f ss OId) (conj Hss Hout)) as Hsome.
        congruence.
    + rewrite IH. split.
      * intros H [|i] f ch Hnth; [discriminate|].
        replace (start + S i) with (S start + i) by lia.
        apply H. exact Hnth.
      * intros H i f ch Hnth.
        replace (S start + i) with (start + S i) by lia.
        apply H. exact Hnth.
Qed.

(** Input checking recognizes exactly the released constructor-rooted sorted expressions. *)
Lemma front_expr_spec : forall V ds (e : fexpr V),
  front_expr (decl_table ds) e = true <-> expr_sorted (lookup_sorts ds) (lookup_kind ds) e.
Proof.
  intros V ds [ns r]. unfold front_expr, expr_sorted. cbn [expr_nodes expr_root].
  destruct (nth_error ns r) as [[f children|v]|] eqn:Hroot.
  - rewrite front_expr_nodes_spec. cbn [Nat.add]. unfold front_expr_condition.
    split.
    + intro H. split; [exists f, children; reflexivity|exact H].
    + intros [_ H]. exact H.
  - split; [discriminate|intros [[f [ch Hbad]] _]; discriminate].
  - split; [discriminate|intros [[f [ch Hbad]] _]; discriminate].
Qed.

(** A growing table keeps a front and a reversed suffix of at most the front's length.
    The remaining room decreases on each push, so testing whether to copy costs one step. *)
Record cell_table (A : Type) : Type := CellTable {
  table_front : list A;
  table_back : list A;
  table_front_size : nat;
  table_back_size : nat;
  table_room : nat
}.

Arguments CellTable {A}.
Arguments table_front {A}.
Arguments table_back {A}.
Arguments table_front_size {A}.
Arguments table_back_size {A}.
Arguments table_room {A}.

TimeFun table_front.
TimeFun table_back.
TimeFun table_front_size.
TimeFun table_back_size.
TimeFun table_room.

Definition table_empty {A} : cell_table A := CellTable [] [] 0 0 0.
TimeFun table_empty.

(** Doubling the front only when the suffix fills pays for all preceding pushes. *)
Definition table_push {A} (x : A) (t : cell_table A) : cell_table A :=
  match table_room t with
  | 0 =>
    let n := S (table_front_size t + table_back_size t) in
    CellTable (table_front t ++ rev_append (x :: table_back t) []) [] n 0 n
  | S room =>
    CellTable (table_front t) (x :: table_back t) (table_front_size t)
      (S (table_back_size t)) room
  end.
TimeFun table_push.

Fixpoint table_sub (n m : nat) : nat :=
  match n, m with
  | S n', S m' => table_sub n' m'
  | _, _ => n
  end.
TimeFun table_sub.

Lemma table_sub_eq : forall n m, table_sub n m = n - m.
Proof.
  induction n as [| n IH]; intros [| m]; cbn; auto.
Qed.

(** Reading index [j] traverses at most its prefix or one suffix no longer than that prefix. *)
Definition table_get {A} (default : A) (j : nat) (t : cell_table A) : A :=
  match nth_error (table_front t) j with
  | Some x => x
  | None =>
    let k := table_sub j (table_front_size t) in
    if Nat.leb (S k) (table_back_size t)
    then match nth_error (table_back t) (table_sub (table_back_size t) (S k)) with
      | Some x => x
      | None => default
      end
    else default
  end.
TimeFun table_get.

Definition table_list {A} (t : cell_table A) : list A :=
  table_front t ++ rev (table_back t).

Definition table_valid {A} (t : cell_table A) : Prop :=
  length (table_front t) = table_front_size t /\
  length (table_back t) = table_back_size t /\
  table_room t + table_back_size t = table_front_size t.

(** The empty cell table satisfies its size and capacity equations. *)
Lemma table_empty_valid : forall A, table_valid (@table_empty A).
Proof.
  intro A. repeat split; reflexivity.
Qed.

(** A table push appends exactly its new cell to the represented sequence. *)
Lemma table_push_list : forall A (x : A) t,
  table_list (table_push x t) = table_list t ++ [x].
Proof.
  intros A x [front back nf nb room].
  unfold table_push, table_list. cbn.
  destruct room; cbn; rewrite ?rev_append_rev, ?app_nil_r; cbn.
  - now rewrite app_assoc.
  - now rewrite app_assoc.
Qed.

(** A table push preserves the exact sizes and remaining capacity. *)
Lemma table_push_valid : forall A (x : A) t,
  table_valid t -> table_valid (table_push x t).
Proof.
  intros A x [front back nf nb room] [Hfront [Hback Hroom]].
  unfold table_valid, table_push in *. cbn in *.
  destruct room; cbn in *.
  - rewrite rev_append_rev, !length_app, length_rev.
    cbn. rewrite Hfront, Hback. repeat split; lia.
  - rewrite Hfront, Hback. repeat split; lia.
Qed.

(** Indexed table access agrees with ordinary list indexing. *)
Lemma table_get_list : forall A (default : A) j t, table_valid t ->
  table_get default j t =
    match nth_error (table_list t) j with Some x => x | None => default end.
Proof.
  intros A default j [front back nf nb room] [Hfront [Hback Hroom]].
  unfold table_get, table_list.
  cbn [table_front table_back table_front_size table_back_size] in *.
  rewrite !table_sub_eq.
  rewrite <- Hfront, <- Hback.
  destruct (nth_error front j) as [x |] eqn:Hget.
  - assert (Hj : j < length front).
    { apply nth_error_Some. rewrite Hget. discriminate. }
    rewrite nth_error_app1 by exact Hj. now rewrite Hget.
  - apply nth_error_None in Hget.
    rewrite nth_error_app2 by exact Hget. rewrite nth_error_rev.
    unfold Nat.ltb.
    destruct (Nat.leb (S (j - length front)) (length back)); reflexivity.
Qed.

(** Each remaining node reads the sorts of the prefix that has already been built. *)
Fixpoint nodes_typed {A} (ds : list decl) (before : list sort) (ns : list (enode A)) : Prop :=
  match ns with
  | [] => True
  | n :: rest =>
    (match n with
     | EApp f children => lookup_kind ds f = Some OId /\
         exists ss, lookup_sorts ds f = Some ss /\
           Forall2 (fun j s => nth_error before j = Some s) children ss
     | ELit _ => True
     end) /\ nodes_typed ds (before ++ [enode_sort n]) rest
  end.

(** Declarative input sorting supplies every prefix premise of the node fold. *)
Lemma expr_nodes_typed : forall A ds (e : fexpr A),
  expr_sorted (lookup_sorts ds) (lookup_kind ds) e ->
  nodes_typed ds [] (expr_nodes A e).
Proof.
  intros A ds [full r] [_ Hnodes]. cbn in Hnodes |- *.
  assert (Hgo : forall rest prefix, full = prefix ++ rest ->
    nodes_typed ds (map enode_sort prefix) rest).
  { induction rest as [| n rest IH]; intros prefix Hfull; cbn [nodes_typed].
    - exact I.
    - split.
      + destruct n as [f children | v]; [| exact I].
        assert (Hnth : nth_error full (length prefix) = Some (EApp f children)).
        { rewrite Hfull, nth_error_app2 by lia. now rewrite Nat.sub_diag. }
        destruct (Hnodes (length prefix) f children Hnth) as [Hkind [ss [Hsort Hchildren]]].
        split; [exact Hkind |]. exists ss. split; [exact Hsort |].
        eapply Forall2_impl; [| exact Hchildren].
        intros j s [Hlt [child [Hchild Hsort']]].
        rewrite Hfull, nth_error_app1 in Hchild by exact Hlt.
        rewrite nth_error_map, Hchild. cbn. now rewrite Hsort'.
      + replace (map enode_sort prefix ++ [enode_sort n])
          with (map enode_sort (prefix ++ [n])) by (rewrite map_app; reflexivity).
        apply (IH (prefix ++ [n])).
        rewrite <- app_assoc. exact Hfull. }
  exact (Hgo full [] eq_refl).
Qed.

Module SaturateCode (V : VALUE_OPS) (I : INDEX_OPS V) (J : JOIN_OPS V I)
    (D : DATABASE_OPS V I) (E : RUN_OPS V I J D) (C : COMPILE_OPS V)
    <: SATURATE_OPS V I J D E C.
  Definition check_front (ds : list decl) (rws : list (rewrite V.t)) (ans : list (rule V.t))
      (es : list (fexpr V.t)) : option reject := front_check ds rws ans es.
  Definition add_node (node : enode V.t) (cells : list (cell V.t)) (db : D.t)
      : cell V.t * D.t :=
    match node with
    | ELit v => (Val v, db)
    | EApp f _ => let '(i, db') := D.make f cells db in (Id i, db')
    end.

  Fixpoint build_nodes (ns : list (enode V.t)) (t : cell_table (cell V.t)) (db : D.t)
      : cell_table (cell V.t) * D.t :=
    match ns with
    | [] => (t, db)
    | n :: rest =>
      let cells :=
        match n with
        | EApp _ children => map (fun j => table_get (Id 1%positive) j t) children
        | ELit _ => []
        end in
      let '(c, db') := add_node n cells db in
      build_nodes rest (table_push c t) db'
    end.

  Definition add_expr (e : fexpr V.t) (db : D.t) : positive * D.t :=
    match e with
    | FExpr _ ns r =>
      let '(t, db') := build_nodes ns table_empty db in
      match table_get (Id 1%positive) r t with
      | Id i => (i, db')
      | Val _ => (1%positive, db')
      end
    end.

  Fixpoint add_inputs (es : list (fexpr V.t)) (db : D.t) : list positive * D.t :=
    match es with
    | [] => ([], db)
    | e :: rest =>
      let '(i, db') := add_expr e db in
      let '(cs, last) := add_inputs rest db' in
      (i :: cs, last)
    end.

  Definition saturate (ds : list decl) (rws : list (rewrite V.t)) (ans : list (rule V.t))
      (lim : limits) (es : list (fexpr V.t)) : reject + (stop * D.t * list positive) :=
    match check_front ds rws ans es with
    | Some err => inl err
    | None =>
      let p := C.compile ds rws ans in
      let cp := E.plan p in
      let '(cs, initial) := add_inputs es (E.load p cp) in
      let '(st, db) := E.run p cp lim initial in
      inr (st, db, cs)
    end.
End SaturateCode.

Module Saturate (V : VALUE) (I : INDEX V) (J : JOIN V I) (D : DATABASE V I)
    (E : RUN V I J D) (C : COMPILE V) <: SATURATE V I J D E C.
  Include SaturateCode V I J D E C.
  Include SATURATE_SPEC V I J D E C.

  (** The paired input fold has the database projection specified by [inputs_db]. *)
  Lemma add_inputs_db : forall es db, snd (add_inputs es db) = inputs_db es db.
  Proof.
    induction es as [| e rest IH]; intro db; cbn [add_inputs inputs_db].
    - reflexivity.
    - destruct (add_expr e db) as [i next] eqn:Hexpr.
      specialize (IH next).
      destruct (add_inputs rest next) as [cs last] eqn:Hrest.
      exact IH.
  Qed.

  (** The input fold returns one class per expression. *)
  Lemma add_inputs_length : forall es db, length (fst (add_inputs es db)) = length es.
  Proof.
    induction es as [| e rest IH]; intro db; cbn [add_inputs].
    - reflexivity.
    - destruct (add_expr e db) as [i next] eqn:Hexpr.
      specialize (IH next).
      destruct (add_inputs rest next) as [cs last] eqn:Hrest.
      cbn in *. now rewrite IH.
  Qed.
  Lemma check_front_spec : forall ds rws ans es,
    check_front ds rws ans es = None <-> front_ok ds rws ans es.
  Proof.
    intros ds rws ans es.
    assert (Hrewrites : Forall (fun rw => front_rewrite (decl_table ds) rw = true) rws <->
      Forall (fun rw => exists g, rewrite_ok (lookup_sorts ds) (lookup_kind ds) rw g) rws).
    { rewrite !Forall_forall. split; intros H rw Hin; apply front_rewrite_spec;
        exact (H rw Hin). }
    assert (Hanalyses : Forall (fun r => front_analysis (decl_table ds) r = true) ans <->
      Forall (analysis_ok (lookup_sorts ds) (lookup_kind ds)) ans).
    { rewrite !Forall_forall. split; intros H r Hin; apply front_analysis_spec;
        exact (H r Hin). }
    assert (Hexprs : Forall (fun e => front_expr (decl_table ds) e = true) es <->
      Forall (expr_sorted (lookup_sorts ds) (lookup_kind ds)) es).
    { rewrite !Forall_forall. split; intros H e Hin; apply front_expr_spec;
        exact (H e Hin). }
    unfold check_front, front_check, front_ok, rules_ok.
    rewrite <- Hrewrites, <- Hanalyses, <- Hexprs, <- !front_first_bad_none.
    destruct (front_first_bad (front_rewrite (decl_table ds)) rws);
      destruct (front_first_bad (front_analysis (decl_table ds)) ans);
      destruct (front_first_bad (front_expr (decl_table ds)) es); intuition discriminate.
  Qed.

  Lemma check_front_report : forall ds rws ans es e,
    check_front ds rws ans es = Some e -> rejected ds rws ans es e.
  Proof.
    intros ds rws ans es e Hcheck. unfold check_front, front_check in Hcheck.
    destruct (front_first_bad (front_rewrite (decl_table ds)) rws) as [n |] eqn:Hrw.
    - injection Hcheck as <-. cbn [rejected].
      destruct (front_first_bad_some _ _ _ _ Hrw) as [rw [Hnth Hfalse]].
      exists rw. split; [exact Hnth |]. intro Hvalid.
      apply front_rewrite_spec in Hvalid. congruence.
    - destruct (front_first_bad (front_analysis (decl_table ds)) ans) as [n |] eqn:Hans.
      + injection Hcheck as <-. cbn [rejected].
        destruct (front_first_bad_some _ _ _ _ Hans) as [r [Hnth Hfalse]].
        exists r. split; [exact Hnth |]. intro Hvalid.
        apply front_analysis_spec in Hvalid. congruence.
      + destruct (front_first_bad (front_expr (decl_table ds)) es) as [n |] eqn:Hes;
          [| discriminate].
        injection Hcheck as <-. cbn [rejected].
        destruct (front_first_bad_some _ _ _ _ Hes) as [x [Hnth Hfalse]].
        exists x. split; [exact Hnth |]. intro Hvalid.
        apply front_expr_spec in Hvalid. congruence.
  Qed.

  Lemma saturate_rejects : forall ds rws ans lim es e,
    saturate ds rws ans lim es = inl e <-> check_front ds rws ans es = Some e.
  Proof.
    intros ds rws ans lim es e. unfold saturate.
    destruct (check_front ds rws ans es) as [err |] eqn:Hcheck.
    - split; intro Heq; now inversion Heq.
    - destruct (add_inputs es (E.load (C.compile ds rws ans)
        (E.plan (C.compile ds rws ans)))) as [cs initial].
      destruct (E.run (C.compile ds rws ans) (E.plan (C.compile ds rws ans)) lim initial)
        as [st db].
      split; discriminate.
  Qed.

  (** Canonicalizing cells preserves their sorts. *)
  Lemma canon_sorts : forall db cells,
    map cell_sort (map (D.canon db) cells) = map cell_sort cells.
  Proof.
    intros db cells. induction cells as [| [i | v] cells IH]; cbn; now rewrite ?IH.
  Qed.

  (** Allocation keeps all old rows and equalities and never lowers the identifier count. *)
  Lemma make_grows : forall f cells db, D.wf db -> kind (D.view db) f = Some OId ->
    (D.ids db <= D.ids (snd (D.make f cells db)))%N /\
    (forall h k o, row (D.view db) h k o -> row (D.view (snd (D.make f cells db))) h k o) /\
    (forall i j, same (D.view db) i j -> same (D.view (snd (D.make f cells db))) i j).
  Proof.
    intros f cells db Hwf Hkind.
    pose proof (D.make_spec f cells db Hwf Hkind) as Hmake.
    destruct (D.make f cells db) as [i next] eqn:Hresult. cbn.
    destruct Hmake as [[j [Hrow [Hi Heq]]] | [Hfresh [Hrow Hextends]]].
    - subst next. split; [apply N.le_refl |]. split; auto.
    - destruct Hextends as [Hids [Hkinds [Hsame Hrows]]].
      split.
      + unfold D.fresh_id in Hfresh. rewrite Hids, Hfresh, N.succ_pos_spec.
        apply N.le_succ_diag_r.
      + split.
        * intros h k o Hrow'. apply (proj2 (Hrows h k o)). now left.
        * intros a b Heq. apply (proj2 (Hsame a b)). now left.
  Qed.

  (** Allocation of correctly sorted children keeps every row correctly sorted. *)
  Lemma make_sorted : forall ds f cells db, D.wf db ->
    view_sorted (lookup_sorts ds) (D.view db) ->
    (forall h, kind (D.view db) h = lookup_kind ds h) ->
    lookup_kind ds f = Some OId -> lookup_sorts ds f = Some (map cell_sort cells) ->
    view_sorted (lookup_sorts ds) (D.view (snd (D.make f cells db))).
  Proof.
    intros ds f cells db Hwf Hsorted Hkind Hf Hcells.
    pose proof (D.make_spec f cells db Hwf (eq_trans (Hkind f) Hf)) as Hmake.
    destruct (D.make f cells db) as [i next] eqn:Hresult. cbn.
    destruct Hmake as [[j [Hrow [Hi Heq]]] | [Hfresh [Hrow Hextends]]].
    - subst next. exact Hsorted.
    - destruct Hextends as [Hids [Hkinds [Hsame Hrows]]].
      intros h k o Hrow'. apply (proj1 (Hrows h k o)) in Hrow'.
      destruct Hrow' as [Hold | [Hh [Hk Ho]]].
      + destruct (Hsorted h k o Hold) as [out [Hsorts [Hout Hres]]].
        exists out. split; [exact Hsorts |]. split; [now rewrite Hkinds | exact Hres].
      + subst h k o. exists OId. split.
        * now rewrite canon_sorts.
        * split; [now rewrite Hkinds, Hkind | reflexivity].
  Qed.

  (** Exact growth of rows and equalities preserves represented expressions. *)
  Lemma represents_mono : forall (w w' : view (V := V.t)) c t,
    (forall f k o, row w f k o -> row w' f k o) ->
    (forall i j, same w i j -> same w' i j) ->
    represents w c t -> represents w' c t.
  Proof.
    intros w w' c t Hrows Hsame Hrep.
    induction Hrep as [v | f k i j args Hrow Heq Hargs IHargs].
    - constructor.
    - eapply rep_app; [exact (Hrows f k _ Hrow) | exact (Hsame i j Heq) |].
      clear Hrow Heq.
      induction IHargs as [| c e ks es Hr Hhead Htail Hall IH].
      + constructor.
      + constructor.
        * exact Hhead.
        * apply IH.
  Qed.

  (** A node returns a cell of its syntactic sort, regardless of the current database. *)
  Lemma add_node_sort : forall node cells db,
    cell_sort (fst (add_node node cells db)) = enode_sort node.
  Proof.
    intros [f children | v] cells db; cbn [add_node enode_sort].
    - destruct (D.make f cells db). reflexivity.
    - reflexivity.
  Qed.

  (** The node table retains its shape and records exactly one cell of each node's sort. *)
  Lemma build_nodes_shape : forall ns t db, table_valid t ->
    table_valid (fst (build_nodes ns t db)) /\
    map cell_sort (table_list (fst (build_nodes ns t db))) =
      map cell_sort (table_list t) ++ map enode_sort ns.
  Proof.
    induction ns as [| n rest IH]; intros t db Hvalid.
    - cbn [build_nodes fst]. split; [exact Hvalid | now rewrite app_nil_r].
    - set (cells := match n with
        | EApp _ children => map (fun j => table_get (Id 1%positive) j t) children
        | ELit _ => []
        end).
      pose proof (add_node_sort n cells db) as Hsort.
      cbn [build_nodes]. fold cells.
      destruct (add_node n cells db) as [c next] eqn:Hnode_result.
      cbn [fst] in Hsort.
      destruct (IH (table_push c t) next (table_push_valid _ c t Hvalid))
        as [Hvalid' Hsorts].
      split; [exact Hvalid' |].
      rewrite Hsorts, table_push_list, map_app. cbn [map].
      rewrite Hsort. now rewrite <- app_assoc.
  Qed.

  (** Reading a valid table agrees with the list-index operation in the plan. *)
  Lemma table_get_nth : forall (default : cell V.t) j t, table_valid t ->
    table_get default j t = nth j (table_list t) default.
  Proof.
    intros default j t Hvalid. rewrite table_get_list by exact Hvalid.
    generalize (table_list t). intro cells. revert j.
    induction cells as [| c rest IH]; intros [| j]; cbn; auto.
  Qed.

  Definition table_allocated (db : D.t) (t : cell_table (cell V.t)) : Prop :=
    Forall (fun c => forall i, c = Id i -> D.allocated db i) (table_list t).

  (** Every typed child index returns an allocated cell of its specified sort. *)
  Lemma table_get_typed : forall db t j s, table_valid t -> table_allocated db t ->
    nth_error (map cell_sort (table_list t)) j = Some s ->
    cell_sort (table_get (Id 1%positive) j t) = s /\
    (forall i, table_get (Id 1%positive) j t = Id i -> D.allocated db i).
  Proof.
    intros db t j s Hvalid Hallocated Hsort.
    rewrite nth_error_map in Hsort.
    destruct (nth_error (table_list t) j) as [c |] eqn:Hnth; [| discriminate].
    cbn in Hsort. inversion Hsort; subst s. rewrite table_get_list by exact Hvalid.
    rewrite Hnth. split; [reflexivity |].
    apply Forall_forall with (x := c) in Hallocated.
    - exact Hallocated.
    - now apply nth_error_In in Hnth.
  Qed.

  (** A complete child tuple has the expected sorts and only allocated identifiers. *)
  Lemma table_children_typed : forall db t children ss, table_valid t -> table_allocated db t ->
    Forall2 (fun j s => nth_error (map cell_sort (table_list t)) j = Some s) children ss ->
    map cell_sort (map (fun j => table_get (Id 1%positive) j t) children) = ss /\
    (forall i, In (Id i) (map (fun j => table_get (Id 1%positive) j t) children) ->
      D.allocated db i).
  Proof.
    intros db t children ss Hvalid Hallocated Htyped.
    induction Htyped as [| j s children ss Hsort Htyped IH]; cbn [map].
    - split; [reflexivity | intros i Hin; contradiction].
    - destruct (table_get_typed db t j s Hvalid Hallocated Hsort) as [Hhead Halloc].
      destruct IH as [Htail Hall]. split.
      + now rewrite Hhead, Htail.
      + intros i [Heq | Hin]; [exact (Halloc i Heq) | exact (Hall i Hin)].
  Qed.

  (** Adding one prepared node preserves sorted rows, layout, allocation and exact growth. *)
  Lemma add_node_properties : forall ds node cells db, D.wf db ->
    view_sorted (lookup_sorts ds) (D.view db) ->
    (forall f, kind (D.view db) f = lookup_kind ds f) ->
    (forall i, In (Id i) cells -> D.allocated db i) ->
    (match node with
     | EApp f _ => lookup_kind ds f = Some OId /\
         lookup_sorts ds f = Some (map cell_sort cells) /\ D.slots_fit db f (S (length cells))
     | ELit _ => cells = []
     end) ->
    D.wf (snd (add_node node cells db)) /\
    view_sorted (lookup_sorts ds) (D.view (snd (add_node node cells db))) /\
    kind (D.view (snd (add_node node cells db))) = kind (D.view db) /\
    D.slots (snd (add_node node cells db)) = D.slots db /\
    (forall i, fst (add_node node cells db) = Id i ->
      D.allocated (snd (add_node node cells db)) i) /\
    (D.ids db <= D.ids (snd (add_node node cells db)))%N /\
    (forall f k o, row (D.view db) f k o ->
      row (D.view (snd (add_node node cells db))) f k o) /\
    (forall i j, same (D.view db) i j -> same (D.view (snd (add_node node cells db))) i j).
  Proof.
    intros ds [f children | v] cells db Hwf Hsorted Hkind Hallocated Hnode.
    - destruct Hnode as [Hf [Hcells Hslots]].
      pose proof (D.wf_make f cells db Hwf Hallocated Hslots) as Hwf'.
      pose proof (D.layout_make f cells db Hwf) as Hlayout.
      pose proof (make_sorted ds f cells db Hwf Hsorted Hkind Hf Hcells) as Hsorted'.
      pose proof (make_grows f cells db Hwf (eq_trans (Hkind f) Hf)) as Hgrowth.
      cbn [add_node]. destruct (D.make f cells db) as [i next] eqn:Hmake.
      cbn in Hwf', Hlayout, Hsorted', Hgrowth |- *.
      destruct Hlayout as [Hkind' [Hslots' [Hupper [Hnew Hpending]]]].
      split; [exact Hwf' |]. split; [exact Hsorted' |].
      split; [exact Hkind' |]. split; [exact Hslots' |]. split.
      + intros j Heq. inversion Heq; subst j. exact Hnew.
      + exact Hgrowth.
    - cbn [add_node]. split; [exact Hwf |]. split; [exact Hsorted |].
      split; [reflexivity |]. split; [reflexivity |]. split.
      + intros i Heq. discriminate.
      + split; [apply N.le_refl |]. split; auto.
  Qed.

  (** The prepared node fold preserves database invariants and its typed cell prefix. *)
  Lemma build_nodes_preserves : forall ds ns t db, D.wf db ->
    view_sorted (lookup_sorts ds) (D.view db) ->
    (forall f, kind (D.view db) f = lookup_kind ds f) ->
    table_valid t -> table_allocated db t ->
    nodes_typed ds (map cell_sort (table_list t)) ns ->
    Forall (fun n => match n with
      | EApp f children => D.slots_fit db f (S (length children))
      | ELit _ => True
      end) ns ->
    let out := build_nodes ns t db in
    D.wf (snd out) /\ view_sorted (lookup_sorts ds) (D.view (snd out)) /\
    kind (D.view (snd out)) = kind (D.view db) /\ D.slots (snd out) = D.slots db /\
    (D.ids db <= D.ids (snd out))%N /\ table_valid (fst out) /\
    table_allocated (snd out) (fst out) /\
    map cell_sort (table_list (fst out)) = map cell_sort (table_list t) ++ map enode_sort ns /\
    (forall f k o, row (D.view db) f k o -> row (D.view (snd out)) f k o) /\
    (forall i j, same (D.view db) i j -> same (D.view (snd out)) i j).
  Proof.
    intros ds ns. induction ns as [| n rest IH]; intros t db Hwf Hsorted Hkind Hvalid
      Hallocated Htyped Hslots.
    - cbn [build_nodes fst snd]. split; [exact Hwf |]. split; [exact Hsorted |].
      split; [reflexivity |]. split; [reflexivity |]. split; [apply N.le_refl |].
      split; [exact Hvalid |]. split; [exact Hallocated |]. split.
      + now rewrite app_nil_r.
      + split; auto.
    - destruct Htyped as [Hnode Htail].
      apply Forall_cons_iff in Hslots. destruct Hslots as [Hslot Hslots].
      set (cells := match n with
        | EApp _ children => map (fun j => table_get (Id 1%positive) j t) children
        | ELit _ => []
        end).
      assert (Hready : (forall i, In (Id i) cells -> D.allocated db i) /\
        match n with
        | EApp f _ => lookup_kind ds f = Some OId /\
            lookup_sorts ds f = Some (map cell_sort cells) /\
            D.slots_fit db f (S (length cells))
        | ELit _ => cells = []
        end).
      { destruct n as [f children | v]; unfold cells; cbn in *.
        - destruct Hnode as [Hf [ss [Hsort Hchildren]]].
          destruct (table_children_typed db t children ss Hvalid Hallocated Hchildren)
            as [Hcells Hids].
          split; [exact Hids |]. split; [exact Hf |]. split.
          + now rewrite Hcells.
          + now rewrite length_map.
        - split; [intros i Hin; contradiction | reflexivity]. }
      destruct Hready as [Hcells Hready].
      pose proof (add_node_properties ds n cells db Hwf Hsorted Hkind Hcells Hready)
        as Hstep.
      pose proof (add_node_sort n cells db) as Hsort.
      cbn [build_nodes]. fold cells.
      destruct (add_node n cells db) as [c next] eqn:Hnode_result.
      cbn in Hstep, Hsort |- *.
      destruct Hstep as [Hwf' [Hsorted' [Hkind' [Hslots' [Hnew [Hids' [Hrows' Hsame']]]]]]].
      assert (Hkind_next : forall f, kind (D.view next) f = lookup_kind ds f).
      { intro f. now rewrite Hkind'. }
      assert (Hvalid_next : table_valid (table_push c t)).
      { now apply table_push_valid. }
      assert (Hallocated_next : table_allocated next (table_push c t)).
      { unfold table_allocated in *. rewrite table_push_list. apply Forall_app. split.
        - eapply Forall_impl; [| exact Hallocated].
          intros old Hold i Heq. specialize (Hold i Heq).
          unfold D.allocated in *. exact (N.le_trans _ _ _ Hold Hids').
        - constructor; [exact Hnew | constructor]. }
      assert (Htyped_next : nodes_typed ds (map cell_sort (table_list (table_push c t))) rest).
      { rewrite table_push_list, map_app. cbn [map]. now rewrite Hsort. }
      assert (Hslots_next : Forall (fun node => match node with
        | EApp f children => D.slots_fit next f (S (length children))
        | ELit _ => True
        end) rest).
      { eapply Forall_impl; [| exact Hslots]. intros [f children | v] Hfits; [| exact I].
        unfold D.slots_fit in *. now rewrite Hslots'. }
      pose proof (IH (table_push c t) next Hwf' Hsorted' Hkind_next Hvalid_next
        Hallocated_next Htyped_next Hslots_next) as Hfinal.
      cbv zeta in Hfinal.
      destruct (build_nodes rest (table_push c t) next) as [result final] eqn:Hrest.
      cbn in Hfinal |- *.
      destruct Hfinal as [Hwf_final [Hsorted_final [Hkind_final [Hslots_final
        [Hids_final [Hvalid_final [Hallocated_final [Hsort_final [Hrows_final Hsame_final]]]]]]]]].
      split; [exact Hwf_final |]. split; [exact Hsorted_final |]. split.
      + now rewrite Hkind_final, Hkind'.
      + split; [now rewrite Hslots_final, Hslots' |]. split.
        * exact (N.le_trans _ _ _ Hids' Hids_final).
        * split; [exact Hvalid_final |]. split; [exact Hallocated_final |]. split.
          -- rewrite Hsort_final, table_push_list, map_app. cbn [map].
             rewrite Hsort. now rewrite <- app_assoc.
          -- split.
             ++ intros f k o Hrow. apply Hrows_final. now apply Hrows'.
             ++ intros i j Heq. apply Hsame_final. now apply Hsame'.
  Qed.

  (** A complete input preserves the database invariants and returns an allocated root. *)
  Lemma add_expr_properties : forall ds e db, D.wf db -> expr_ok ds db e ->
    view_sorted (lookup_sorts ds) (D.view db) ->
    D.wf (snd (add_expr e db)) /\
    view_sorted (lookup_sorts ds) (D.view (snd (add_expr e db))) /\
    kind (D.view (snd (add_expr e db))) = kind (D.view db) /\
    D.slots (snd (add_expr e db)) = D.slots db /\
    D.allocated (snd (add_expr e db)) (fst (add_expr e db)) /\
    (D.ids db <= D.ids (snd (add_expr e db)))%N /\
    (forall f k o, row (D.view db) f k o ->
      row (D.view (snd (add_expr e db))) f k o) /\
    (forall i j, same (D.view db) i j ->
      same (D.view (snd (add_expr e db))) i j).
  Proof.
    intros ds [ns root_index] db Hwf [Hexpr [Hkind Hslots]] Hsorted.
    pose proof (expr_nodes_typed V.t ds (FExpr V.t ns root_index) Hexpr) as Htyped.
    assert (Hallocated : table_allocated db (@table_empty (cell V.t))).
    { constructor. }
    pose proof (build_nodes_preserves ds ns table_empty db Hwf Hsorted Hkind
      (table_empty_valid (cell V.t)) Hallocated Htyped Hslots) as Hbuild.
    cbv zeta in Hbuild. unfold add_expr.
    destruct (build_nodes ns table_empty db) as [t final] eqn:Hresult.
    cbn [fst snd table_list table_empty app map] in Hbuild.
    destruct Hbuild as [Hwf' [Hsorted' [Hkind' [Hslots' [Hids'
      [Hvalid [Hallocated' [Hsorts [Hrows Hsame]]]]]]]]].
    change (map cell_sort (table_list t) = map enode_sort ns) in Hsorts.
    destruct Hexpr as [[f [children Hroot]] Hnodes].
    assert (Hroot_sort : nth_error (map cell_sort (table_list t)) root_index = Some SId).
    { rewrite Hsorts, nth_error_map. cbn [expr_nodes expr_root] in Hroot.
      rewrite Hroot. reflexivity. }
    destruct (table_get_typed final t root_index SId Hvalid Hallocated' Hroot_sort)
      as [Hsort Hroot_allocated].
    destruct (table_get (Id 1%positive) root_index t) as [i | v] eqn:Hget;
      [| discriminate Hsort].
    cbn [fst snd]. split; [exact Hwf' |]. split; [exact Hsorted' |].
    split; [exact Hkind' |]. split; [exact Hslots' |]. split.
    - exact (Hroot_allocated i eq_refl).
    - split; [exact Hids' |]. split; assumption.
  Qed.

  (** Finding a declaration gives both of its public lookup fields. *)
  Lemma found_decl_fields : forall ds f d,
    find (fun d => Pos.eqb (name d) f) ds = Some d ->
    lookup_sorts ds f = Some (arg_sorts d) /\ lookup_kind ds f = Some (out d).
  Proof.
    induction ds as [| head rest IH]; intros f d Hfind; [discriminate |].
    cbn [find lookup_sorts lookup_kind] in Hfind |- *.
    destruct (Pos.eqb (name head) f).
    - inversion Hfind; subst d. split; reflexivity.
    - exact (IH f d Hfind).
  Qed.

  (** A checked loaded plan provides enough slots for each well-sorted input node. *)
  Lemma loaded_expr_ok : forall p cp ds db e, decls V.t p = ds ->
    E.plans_ok p cp -> E.loaded p cp db ->
    expr_sorted (lookup_sorts ds) (lookup_kind ds) e -> expr_ok ds db e.
  Proof.
    intros p cp ds db e Hdecls Hplan [Hkind [Hslots Hsorted]] Hexpr.
    split; [exact Hexpr |]. split.
    - intro f. rewrite Hkind. unfold program_kind. now rewrite Hdecls.
    - apply Forall_forall. intros [f children | v] Hin; [| exact I].
      apply In_nth_error in Hin. destruct Hin as [i Hnth].
      destruct Hexpr as [Hroot Hnodes].
      destruct (Hnodes i f children Hnth) as [Hf [ss [Hss Hchildren]]].
      unfold D.slots_fit. intros perm Hin. rewrite Hslots in Hin.
      destruct (E.check_plan_slots p cp f perm Hplan Hin)
        as [d [Hfind [Hdistinct Hbounds]]].
      rewrite Hdecls in Hfind.
      destruct (found_decl_fields ds f d Hfind) as [Hsorts Hout].
      assert (Hout' : out d = OId) by congruence.
      assert (Hsorts' : arg_sorts d = ss) by congruence.
      pose proof (Forall2_length Hchildren) as Hlength.
      split; [exact Hdistinct |].
      rewrite Hout', Hsorts' in Hbounds. cbn in Hbounds.
      replace (S (length children)) with (length ss + 1) by lia.
      exact Hbounds.
  Qed.

  (** Loading any program initializes its declared kinds, planned slots and empty rows. *)
  Lemma load_properties : forall p cp, D.wf (E.load p cp) /\ E.loaded p cp (E.load p cp).
  Proof.
    intros p cp. rewrite E.load_spec. split; [apply D.wf_init |].
    unfold E.loaded, program_kind, program_sorts. split.
    - intro f.
      exact (proj1 (proj2 (proj2
        (D.init_view (decls V.t p) (Egglog.Syntax.slots V.t cp) f [] None 1 1)))).
    - split.
      + exact (proj1 (proj2 (proj2 (proj2
          (D.init_view (decls V.t p) (Egglog.Syntax.slots V.t cp) 1 [] None 1 1))))).
      + intros f k o Hrow.
        apply (proj1 (proj1
          (D.init_view (decls V.t p) (Egglog.Syntax.slots V.t cp) f k o 1 1))) in Hrow.
        contradiction.
  Qed.

  (** Input admissibility depends on the database kinds and slot layout only. *)
  Lemma expr_ok_layout : forall ds db db' e,
    kind (D.view db') = kind (D.view db) -> D.slots db' = D.slots db ->
    expr_ok ds db e -> expr_ok ds db' e.
  Proof.
    intros ds db db' e Hkind Hslots [Hexpr [Hkinds Hfits]].
    split; [exact Hexpr |]. split.
    - intro f. now rewrite Hkind.
    - eapply Forall_impl; [| exact Hfits]. intros [f children | v] Hfit; [| exact I].
      unfold D.slots_fit in *. now rewrite Hslots.
  Qed.

  (** Adding all inputs preserves the database layout and every old row and equality. *)
  Lemma add_inputs_properties : forall ds es db, D.wf db ->
    view_sorted (lookup_sorts ds) (D.view db) -> Forall (expr_ok ds db) es ->
    D.wf (snd (add_inputs es db)) /\
    view_sorted (lookup_sorts ds) (D.view (snd (add_inputs es db))) /\
    kind (D.view (snd (add_inputs es db))) = kind (D.view db) /\
    D.slots (snd (add_inputs es db)) = D.slots db /\
    (D.ids db <= D.ids (snd (add_inputs es db)))%N /\
    (forall f k o, row (D.view db) f k o ->
      row (D.view (snd (add_inputs es db))) f k o) /\
    (forall i j, same (D.view db) i j ->
      same (D.view (snd (add_inputs es db))) i j).
  Proof.
    intros ds es. induction es as [| e rest IH]; intros db Hwf Hsorted Hexprs.
    - cbn [add_inputs snd]. split; [exact Hwf |]. split; [exact Hsorted |].
      split; [reflexivity |]. split; [reflexivity |]. split; [apply N.le_refl |].
      split; auto.
    - apply Forall_cons_iff in Hexprs. destruct Hexprs as [Hexpr Hrest].
      destruct (add_expr_properties ds e db Hwf Hexpr Hsorted)
        as [Hwf' [Hsorted' [Hkind [Hslots [Hnew [Hids [Hrows Hsame]]]]]]].
      assert (Hrest' : Forall (expr_ok ds (snd (add_expr e db))) rest).
      { eapply Forall_impl; [| exact Hrest]. intros x Hx.
        exact (expr_ok_layout ds db (snd (add_expr e db)) x Hkind Hslots Hx). }
      pose proof (IH (snd (add_expr e db)) Hwf' Hsorted' Hrest') as Hfinal.
      cbn [add_inputs]. destruct (add_expr e db) as [i next] eqn:Hexpr_result.
      cbn [snd] in *.
      destruct (add_inputs rest next) as [cs final] eqn:Hrest_result.
      cbn [snd] in *.
      destruct Hfinal as [Hwf_final [Hsorted_final [Hkind_final [Hslots_final
        [Hids_final [Hrows_final Hsame_final]]]]]].
      split; [exact Hwf_final |]. split; [exact Hsorted_final |]. split.
      + now rewrite Hkind_final, Hkind.
      + split; [now rewrite Hslots_final, Hslots |]. split.
        * exact (N.le_trans _ _ _ Hids Hids_final).
        * split.
          -- intros f k o Hrow. apply Hrows_final. now apply Hrows.
          -- intros i' j' Heq. apply Hsame_final. now apply Hsame.
  Qed.

  (** Any invariant kept by one prepared node is kept by the complete node fold. *)
  Lemma build_nodes_frame : forall ds
    (P : list (enode V.t) -> cell_table (cell V.t) -> D.t -> Prop),
    (forall n rest t db, D.wf db -> view_sorted (lookup_sorts ds) (D.view db) ->
      (forall f, kind (D.view db) f = lookup_kind ds f) ->
      table_valid t -> table_allocated db t ->
      nodes_typed ds (map cell_sort (table_list t)) (n :: rest) ->
      Forall (fun node => match node with
        | EApp f children => D.slots_fit db f (S (length children))
        | ELit _ => True
        end) (n :: rest) ->
      P (n :: rest) t db ->
      let cells := match n with
        | EApp _ children => map (fun j => table_get (Id 1%positive) j t) children
        | ELit _ => []
        end in
      P rest (table_push (fst (add_node n cells db)) t) (snd (add_node n cells db))) ->
    forall ns t db, D.wf db -> view_sorted (lookup_sorts ds) (D.view db) ->
      (forall f, kind (D.view db) f = lookup_kind ds f) ->
      table_valid t -> table_allocated db t ->
      nodes_typed ds (map cell_sort (table_list t)) ns ->
      Forall (fun node => match node with
        | EApp f children => D.slots_fit db f (S (length children))
        | ELit _ => True
        end) ns -> P ns t db ->
      P [] (fst (build_nodes ns t db)) (snd (build_nodes ns t db)).
  Proof.
    intros ds P Hstep ns. induction ns as [| n rest IH]; intros t db Hwf Hsorted Hkind
      Hvalid Hallocated Htyped Hslots HP; [exact HP |].
    pose proof (Hstep n rest t db Hwf Hsorted Hkind Hvalid Hallocated Htyped Hslots HP)
      as HPnext.
    destruct Htyped as [Hnode Htail].
    apply Forall_cons_iff in Hslots. destruct Hslots as [Hslot Hslots].
    assert (Hsingle : nodes_typed ds (map cell_sort (table_list t)) [n]).
    { split; [exact Hnode | exact I]. }
    assert (Hslot_single : Forall (fun node => match node with
      | EApp f children => D.slots_fit db f (S (length children))
      | ELit _ => True
      end) [n]) by (constructor; [exact Hslot | constructor]).
    pose proof (build_nodes_preserves ds [n] t db Hwf Hsorted Hkind Hvalid Hallocated
      Hsingle Hslot_single) as Hnext.
    set (cells := match n with
      | EApp _ children => map (fun j => table_get (Id 1%positive) j t) children
      | ELit _ => []
      end) in *.
    cbv zeta in HPnext. fold cells in HPnext.
    cbn [build_nodes] in Hnext |- *. fold cells in Hnext |- *.
    destruct (add_node n cells db) as [c next] eqn:Hnode_result.
    cbn [build_nodes fst snd] in Hnext, HPnext |- *.
    destruct Hnext as [Hwf' [Hsorted' [Hkind' [Hslots' [Hids'
      [Hvalid' [Hallocated' [Hsorts Hgrowth]]]]]]]].
    apply IH; try assumption.
    - intro f. now rewrite Hkind'.
    - rewrite Hsorts. exact Htail.
    - eapply Forall_impl; [| exact Hslots]. intros [f children | v] Hfits; [| exact I].
      unfold D.slots_fit in *. now rewrite Hslots'.
  Qed.

  (** Adding a constructor or a literal preserves satisfaction by some valuation. *)
  Lemma add_node_sat : forall (M : model (V := V.t)) nu node cells db, D.wf db ->
    (match node with EApp f _ => kind (D.view db) f = Some OId | ELit _ => True end) ->
    (forall i, In (Id i) cells -> D.allocated db i) -> sat V.merge M nu (D.view db) ->
    exists nu', sat V.merge M nu' (D.view (snd (add_node node cells db))).
  Proof.
    intros M nu [f children | v] cells db Hwf Hkind Hallocated Hsat.
    - pose proof (D.make_sat M nu db f cells Hwf Hkind Hallocated Hsat) as Hmake.
      cbn [add_node]. destruct (D.make f cells db) as [i next]. cbn [snd].
      destruct Hmake as [nu' [Hstable [Hvalue Hsat']]]. now exists nu'.
    - exists nu. exact Hsat.
  Qed.

  (** The node fold preserves satisfaction while giving new constructors their meanings. *)
  Lemma build_nodes_sat : forall ds ns t db (M : model (V := V.t)), D.wf db ->
    view_sorted (lookup_sorts ds) (D.view db) ->
    (forall f, kind (D.view db) f = lookup_kind ds f) ->
    table_valid t -> table_allocated db t ->
    nodes_typed ds (map cell_sort (table_list t)) ns ->
    Forall (fun node => match node with
      | EApp f children => D.slots_fit db f (S (length children))
      | ELit _ => True
      end) ns ->
    (exists nu, sat V.merge M nu (D.view db)) ->
    exists nu, sat V.merge M nu (D.view (snd (build_nodes ns t db))).
  Proof.
    intros ds ns t db M Hwf Hsorted Hkind Hvalid Hallocated Htyped Hslots Hsat.
    apply (build_nodes_frame ds
      (fun _ _ next => exists nu, sat V.merge M nu (D.view next)))
      with (ns := ns) (t := t) (db := db); try assumption.
    intros [f children | v] rest cells_db current Hwf' Hsorted' Hkind' Hvalid'
      Hallocated' Htyped' Hslots' [nu Hsat']; cbv zeta.
    - destruct Htyped' as [[Hf [ss [Hss Hchildren]]] Htail].
      destruct (table_children_typed current cells_db children ss Hvalid' Hallocated'
        Hchildren) as [Hsorts Hids].
      eapply add_node_sat; [exact Hwf' | | exact Hids | exact Hsat'].
      now rewrite Hkind'.
    - eapply add_node_sat; [exact Hwf' | exact I | | exact Hsat'].
      intros i Hin. contradiction.
  Qed.

  (** Adding one well-sorted expression preserves satisfaction by some valuation. *)
  Lemma add_expr_sat : forall ds e db (M : model (V := V.t)), D.wf db ->
    expr_ok ds db e -> view_sorted (lookup_sorts ds) (D.view db) ->
    (exists nu, sat V.merge M nu (D.view db)) ->
    exists nu, sat V.merge M nu (D.view (snd (add_expr e db))).
  Proof.
    intros ds [ns root_index] db M Hwf [Hexpr [Hkind Hslots]] Hsorted Hsat.
    pose proof (expr_nodes_typed V.t ds (FExpr V.t ns root_index) Hexpr) as Htyped.
    assert (Hallocated : table_allocated db (@table_empty (cell V.t))) by constructor.
    pose proof (build_nodes_sat ds ns table_empty db M Hwf Hsorted Hkind
      (table_empty_valid (cell V.t)) Hallocated Htyped Hslots Hsat) as Hfinal.
    unfold add_expr. destruct (build_nodes ns table_empty db) as [t final].
    destruct (table_get (Id 1%positive) root_index t); exact Hfinal.
  Qed.

  (** Adding an ordered list of admissible inputs preserves model satisfaction. *)
  Lemma add_inputs_sat : forall ds es db (M : model (V := V.t)), D.wf db ->
    view_sorted (lookup_sorts ds) (D.view db) -> Forall (expr_ok ds db) es ->
    (exists nu, sat V.merge M nu (D.view db)) ->
    exists nu, sat V.merge M nu (D.view (snd (add_inputs es db))).
  Proof.
    intros ds es. induction es as [| e rest IH]; intros db M Hwf Hsorted Hexprs Hsat.
    - exact Hsat.
    - apply Forall_cons_iff in Hexprs. destruct Hexprs as [Hexpr Hrest].
      pose proof (add_expr_sat ds e db M Hwf Hexpr Hsorted Hsat) as Hsat'.
      destruct (add_expr_properties ds e db Hwf Hexpr Hsorted)
        as [Hwf' [Hsorted' [Hkind [Hslots Hgrowth]]]].
      assert (Hrest' : Forall (expr_ok ds (snd (add_expr e db))) rest).
      { eapply Forall_impl; [| exact Hrest]. intros x Hx.
        exact (expr_ok_layout ds db (snd (add_expr e db)) x Hkind Hslots Hx). }
      pose proof (IH (snd (add_expr e db)) M Hwf' Hsorted' Hrest' Hsat') as Hfinal.
      cbn [add_inputs]. destruct (add_expr e db) as [i next] eqn:Hexpr_result.
      cbn [snd] in Hfinal. destruct (add_inputs rest next) as [cs final]. exact Hfinal.
  Qed.

  (** Empty loaded rows satisfy every model closed under the declared lattice merges. *)
  Lemma load_sat : forall (M : model (V := V.t)) p cp,
    (forall f m k a b, program_kind p f = Some (OLat m) ->
      lat M f k a -> lat M f k b -> lat M f k (V.merge m a b)) ->
    exists nu, sat V.merge M nu (D.view (E.load p cp)).
  Proof.
    intros M p cp Hmerge. rewrite E.load_spec.
    exists (fun _ => con M 1%positive []). split.
    - intros f k o Hrow.
      apply (proj1 (proj1
        (D.init_view (decls V.t p) (Egglog.Syntax.slots V.t cp) f k o 1 1))) in Hrow.
      contradiction.
    - split.
      + intros i j Heq. reflexivity.
      + intros f m k a b Hkind Ha Hb. apply (Hmerge f m k a b); try assumption.
        unfold program_kind. rewrite <- Hkind. symmetry.
        exact (proj1 (proj2 (proj2
          (D.init_view (decls V.t p) (Egglog.Syntax.slots V.t cp) f [] None 1 1)))).
  Qed.

  (** Accepted inputs admit a satisfying valuation in every merge-closed model. *)
  Lemma inputs_sat : forall (M : model (V := V.t)) ds rws ans es,
    front_ok ds rws ans es ->
    (forall f m k a b, lookup_kind ds f = Some (OLat m) ->
      lat M f k a -> lat M f k b -> lat M f k (V.merge m a b)) ->
    let p := C.compile ds rws ans in
    exists nu, sat V.merge M nu (D.view (snd (add_inputs es (E.load p (E.plan p))))).
  Proof.
    intros M ds rws ans es [Hrules Hexprs] Hmerge. cbv zeta.
    set (p := C.compile ds rws ans). set (cp := E.plan p).
    assert (Hdecls : decls V.t p = ds) by apply C.compile_program.
    assert (Hplan : E.plans_ok p cp).
    { apply E.plan_checked. now apply C.compile_sorted. }
    destruct (load_properties p cp) as [Hwf Hloaded].
    destruct Hloaded as [Hkind [Hslots Hsorted]].
    assert (Hsorted' : view_sorted (lookup_sorts ds) (D.view (E.load p cp))).
    { unfold program_sorts in Hsorted. now rewrite Hdecls in Hsorted. }
    assert (Hinputs : Forall (expr_ok ds (E.load p cp)) es).
    { eapply Forall_impl; [| exact Hexprs]. intros e Hexpr.
      eapply loaded_expr_ok; [exact Hdecls | exact Hplan | | exact Hexpr].
      split; [exact Hkind |]. split; assumption. }
    apply (add_inputs_sat ds es (E.load p cp) M Hwf Hsorted' Hinputs).
    apply load_sat. unfold program_kind. now rewrite Hdecls.
  Qed.

  (** Equal identifiers represent the same expressions. *)
  Lemma represents_same : forall db i j t, D.wf db -> same (D.view db) i j ->
    represents (D.view db) (Id j) t -> represents (D.view db) (Id i) t.
  Proof.
    intros db i j t Hwf Hij Hrep.
    inversion Hrep as [v | f k i' j' args Hrow Hsame Hargs]; subst.
    eapply rep_app; [exact Hrow | | exact Hargs].
    apply (proj2 (D.same_repr db i j' Hwf)).
    transitivity (D.repr db j).
    - exact (proj1 (D.same_repr db i j Hwf) Hij).
    - exact (proj1 (D.same_repr db j j' Hwf) Hsame).
  Qed.

  (** Node insertion preserves allocation and layout without requiring old rows to be sorted. *)
  Lemma add_node_ready : forall node cells db, D.wf db ->
    (forall i, In (Id i) cells -> D.allocated db i) ->
    (match node with
      | EApp f _ => kind (D.view db) f = Some OId /\
          D.slots_fit db f (S (length cells))
      | ELit _ => True
      end) ->
    D.wf (snd (add_node node cells db)) /\
    kind (D.view (snd (add_node node cells db))) = kind (D.view db) /\
    D.slots (snd (add_node node cells db)) = D.slots db /\
    (forall i, fst (add_node node cells db) = Id i ->
      D.allocated (snd (add_node node cells db)) i) /\
    (D.ids db <= D.ids (snd (add_node node cells db)))%N /\
    (forall f k o, row (D.view db) f k o ->
      row (D.view (snd (add_node node cells db))) f k o) /\
    (forall i j, same (D.view db) i j ->
      same (D.view (snd (add_node node cells db))) i j).
  Proof.
    intros [f children | v] cells db Hwf Hallocated Hnode.
    - destruct Hnode as [Hkind Hfits].
      pose proof (D.wf_make f cells db Hwf Hallocated Hfits) as Hwf'.
      pose proof (D.layout_make f cells db Hwf) as Hlayout.
      pose proof (make_grows f cells db Hwf Hkind) as Hgrowth.
      cbn [add_node]. destruct (D.make f cells db) as [i next] eqn:Hmake.
      cbn [fst snd] in Hwf', Hlayout, Hgrowth |- *.
      destruct Hlayout as [Hkind' [Hslots [Hupper [Hnew Hpending]]]].
      split; [exact Hwf' |]. split; [exact Hkind' |]. split; [exact Hslots |]. split.
      + intros j Heq. inversion Heq; subst j. exact Hnew.
      + exact Hgrowth.
    - cbn [add_node fst snd]. split; [exact Hwf |]. split; [reflexivity |].
      split; [reflexivity |]. split; [intros i Heq; discriminate |].
      split; [apply N.le_refl |]. split; auto.
  Qed.

  (** The node fold transports invariants even when its preexisting rows lack sort evidence. *)
  Lemma build_nodes_frame_ready : forall ds
    (P : list (enode V.t) -> cell_table (cell V.t) -> D.t -> Prop),
    (forall n rest t db, D.wf db ->
      (forall f, kind (D.view db) f = lookup_kind ds f) ->
      table_valid t -> table_allocated db t ->
      nodes_typed ds (map cell_sort (table_list t)) (n :: rest) ->
      Forall (fun node => match node with
        | EApp f children => D.slots_fit db f (S (length children))
        | ELit _ => True
        end) (n :: rest) ->
      P (n :: rest) t db ->
      let cells := match n with
        | EApp _ children => map (fun j => table_get (Id 1%positive) j t) children
        | ELit _ => []
        end in
      P rest (table_push (fst (add_node n cells db)) t) (snd (add_node n cells db))) ->
    forall ns t db, D.wf db ->
      (forall f, kind (D.view db) f = lookup_kind ds f) ->
      table_valid t -> table_allocated db t ->
      nodes_typed ds (map cell_sort (table_list t)) ns ->
      Forall (fun node => match node with
        | EApp f children => D.slots_fit db f (S (length children))
        | ELit _ => True
        end) ns -> P ns t db ->
      P [] (fst (build_nodes ns t db)) (snd (build_nodes ns t db)).
  Proof.
    intros ds P Hstep ns. induction ns as [| n rest IH]; intros t db Hwf Hkind Hvalid
      Hallocated Htyped Hslots HP; [exact HP |].
    pose proof (Hstep n rest t db Hwf Hkind Hvalid Hallocated Htyped Hslots HP) as HPnext.
    destruct Htyped as [Hnode Htail].
    apply Forall_cons_iff in Hslots. destruct Hslots as [Hslot Hslots].
    set (cells := match n with
      | EApp _ children => map (fun j => table_get (Id 1%positive) j t) children
      | ELit _ => []
      end) in *.
    assert (Hready : (forall i, In (Id i) cells -> D.allocated db i) /\
      match n with
      | EApp f _ => kind (D.view db) f = Some OId /\
          D.slots_fit db f (S (length cells))
      | ELit _ => True
      end).
    { destruct n as [f children | v]; unfold cells; cbn in *.
      - destruct Hnode as [Hf [ss [Hss Hchildren]]].
        destruct (table_children_typed db t children ss Hvalid Hallocated Hchildren)
          as [Hsorts Hids].
        split; [exact Hids |]. split; [now rewrite Hkind | now rewrite length_map].
      - split; [intros i Hin; contradiction | exact I]. }
    destruct Hready as [Hcells Hready].
    pose proof (add_node_ready n cells db Hwf Hcells Hready) as Hnext.
    pose proof (add_node_sort n cells db) as Hsort.
    cbv zeta in HPnext. fold cells in HPnext.
    cbn [build_nodes]. fold cells.
    destruct (add_node n cells db) as [c next] eqn:Hnode_result.
    cbn [fst snd] in Hnext, Hsort, HPnext |- *.
    destruct Hnext as [Hwf' [Hkind' [Hslots' [Hnew [Hids' Hgrowth]]]]].
    apply IH; try assumption.
    - intro f. now rewrite Hkind'.
    - now apply table_push_valid.
    - unfold table_allocated in *. rewrite table_push_list. apply Forall_app. split.
      + eapply Forall_impl; [| exact Hallocated]. intros old Hold i Heq.
        specialize (Hold i Heq). unfold D.allocated in *.
        exact (N.le_trans _ _ _ Hold Hids').
      + constructor; [exact Hnew | constructor].
    - rewrite table_push_list, map_app. cbn [map]. now rewrite Hsort.
    - eapply Forall_impl; [| exact Hslots]. intros [f children | v] Hfits; [| exact I].
      unfold D.slots_fit in *. now rewrite Hslots'.
  Qed.

  (** Replacing an identifier by its representative preserves its represented expression. *)
  Lemma canon_represents : forall db c e, D.wf db -> represents (D.view db) c e ->
    represents (D.view db) (D.canon db c) e.
  Proof.
    intros db [i | v] e Hwf Hrep; [| exact Hrep].
    apply (represents_same db (D.repr db i) i e Hwf); [| exact Hrep].
    apply (proj2 (D.same_repr db (D.repr db i) i Hwf)). now apply D.repr_idem.
  Qed.

  (** A constructor insertion represents the constructor applied to its represented children. *)
  Lemma make_represents : forall db f cells args, D.wf db ->
    kind (D.view db) f = Some OId -> D.wf (snd (D.make f cells db)) ->
    Forall2 (represents (D.view db)) cells args ->
    represents (D.view (snd (D.make f cells db))) (Id (fst (D.make f cells db)))
      (Model.EApp f args).
  Proof.
    intros db f cells args Hwf Hkind Hwf' Hargs.
    pose proof (D.make_spec f cells db Hwf Hkind) as Hmake.
    pose proof (make_grows f cells db Hwf Hkind) as Hgrowth.
    destruct (D.make f cells db) as [i next] eqn:Hresult.
    cbn [fst snd] in Hwf', Hgrowth |- *.
    destruct Hgrowth as [Hids [Hrows Hsame]].
    assert (Hcanonical : Forall2 (represents (D.view next)) (map (D.canon db) cells) args).
    { clear Hmake Hresult. induction Hargs as [| c e cs es Hrep Hargs IH]; cbn [map].
      - constructor.
      - constructor; [| exact IH].
        eapply represents_mono; [exact Hrows | exact Hsame |].
        now apply canon_represents. }
    destruct Hmake as [[j [Hrow [Hi Heq]]] | [Hfresh [Hrow Hextends]]].
    - subst next i. eapply rep_app; [exact Hrow | | exact Hcanonical].
      apply (proj2 (D.same_repr db (D.repr db j) j Hwf)). now apply D.repr_idem.
    - eapply rep_app; [exact Hrow | | exact Hcanonical].
      apply (proj2 (D.same_repr next i i Hwf')). reflexivity.
  Qed.

  (** Extending a valid table does not change an earlier lookup. *)
  Lemma table_get_push_old : forall (default x : cell V.t) t j, table_valid t ->
    j < length (table_list t) -> table_get default j (table_push x t) = table_get default j t.
  Proof.
    intros default x t j Hvalid Hlt.
    rewrite (table_get_list _ default j (table_push x t) (table_push_valid _ x t Hvalid)).
    rewrite (table_get_list _ default j t Hvalid), table_push_list.
    now rewrite nth_error_app1 by exact Hlt.
  Qed.

  (** The next lookup after a valid table's old prefix is the newly added cell. *)
  Lemma table_get_push_last : forall (default x : cell V.t) t, table_valid t ->
    table_get default (length (table_list t)) (table_push x t) = x.
  Proof.
    intros default x t Hvalid.
    rewrite (table_get_list _ default _ (table_push x t) (table_push_valid _ x t Hvalid)).
    rewrite table_push_list, nth_error_app2 by lia.
    now rewrite Nat.sub_diag.
  Qed.

  (** Every recorded cell represents all unfoldings of its corresponding flat node. *)
  Definition table_represents (full : list (enode V.t)) (db : D.t)
      (t : cell_table (cell V.t)) : Prop :=
    forall j e, j < length (table_list t) -> unfolds_expr full j e ->
      represents (D.view db) (table_get (Id 1%positive) j t) e.

  (** One prepared node extends the represented prefix of the complete flat expression. *)
  Lemma table_represents_step : forall ds full prefix n rest t db,
    full = prefix ++ n :: rest -> length prefix = length (table_list t) ->
    D.wf db -> (forall f, kind (D.view db) f = lookup_kind ds f) ->
    table_valid t -> table_allocated db t ->
    nodes_typed ds (map cell_sort (table_list t)) (n :: rest) ->
    (match n with EApp f children => D.slots_fit db f (S (length children))
      | ELit _ => True end) -> table_represents full db t ->
    let cells := match n with
      | EApp _ children => map (fun j => table_get (Id 1%positive) j t) children
      | ELit _ => []
      end in
    table_represents full (snd (add_node n cells db))
      (table_push (fst (add_node n cells db)) t).
  Proof.
    intros ds full prefix n rest t db Hfull Hlength Hwf Hkind Hvalid Hallocated
      [Hnode Htail] Hslot Htable.
    set (cells := match n with
      | EApp _ children => map (fun j => table_get (Id 1%positive) j t) children
      | ELit _ => []
      end).
    assert (Hready : (forall i, In (Id i) cells -> D.allocated db i) /\
      match n with
      | EApp f _ => kind (D.view db) f = Some OId /\
          D.slots_fit db f (S (length cells))
      | ELit _ => True
      end).
    { destruct n as [f children | v]; unfold cells; cbn in *.
      - destruct Hnode as [Hf [ss [Hss Hchildren]]].
        destruct (table_children_typed db t children ss Hvalid Hallocated Hchildren)
          as [Hsorts Hids].
        split; [exact Hids |]. split; [now rewrite Hkind | now rewrite length_map].
      - split; [intros i Hin; contradiction | exact I]. }
    destruct Hready as [Hcells Hready].
    pose proof (add_node_ready n cells db Hwf Hcells Hready) as Hnext.
    cbv zeta. fold cells.
    destruct (add_node n cells db) as [c next] eqn:Hnode_result.
    cbn [fst snd] in Hnext |- *.
    destruct Hnext as [Hwf' [Hkind' [Hslots' [Hnew [Hids' [Hrows Hsame]]]]]].
    intros j e Hbound Hunfold.
    rewrite table_push_list, length_app in Hbound. cbn [length] in Hbound.
    destruct (Nat.lt_ge_cases j (length (table_list t))) as [Hlt | Hge].
    - rewrite table_get_push_old by assumption.
      eapply represents_mono; [exact Hrows | exact Hsame |].
      exact (Htable j e Hlt Hunfold).
    - assert (Hj : j = length (table_list t)) by lia. subst j.
      rewrite table_get_push_last by exact Hvalid.
      assert (Hnth_node : nth_error full (length (table_list t)) = Some n).
      { rewrite Hfull, <- Hlength, nth_error_app2 by lia. now rewrite Nat.sub_diag. }
      destruct n as [f children | v].
      + inversion Hunfold as [i v Hnth | i f' children' args Hnth Hbefore Hargs];
          subst; try congruence.
        rewrite Hnth_node in Hnth. injection Hnth as <- <-.
        assert (Hchildren_rep : Forall2 (represents (D.view db)) cells args).
        { unfold cells. clear - Htable Hargs Hbefore. revert Hbefore.
          induction Hargs as [| j e js es Hunfold Hargs IH]; intro Hbefore; cbn [map].
          - constructor.
          - apply Forall_cons_iff in Hbefore. destruct Hbefore as [Hlt Hbefore].
            constructor; [exact (Htable j e Hlt Hunfold) | now apply IH]. }
        cbn [add_node] in Hnode_result.
        destruct (D.make f cells db) as [i final] eqn:Hmake.
        inversion Hnode_result; subst c final.
        pose proof (make_represents db f cells args Hwf (proj1 Hready)) as Hrep.
        rewrite Hmake in Hrep. cbn [fst snd] in Hrep.
        exact (Hrep Hwf' Hchildren_rep).
      + inversion Hunfold as [i v' Hnth | i f children args Hnth Hbefore Hargs];
          subst; try congruence.
        rewrite Hnth_node in Hnth. injection Hnth as <-.
        cbn [add_node] in Hnode_result. inversion Hnode_result; subst c next. constructor.
  Qed.

  (** The completed node fold represents every unfolding at every node in the input. *)
  Lemma build_nodes_represents : forall ds full db, D.wf db ->
    (forall f, kind (D.view db) f = lookup_kind ds f) -> nodes_typed ds [] full ->
    Forall (fun node => match node with
      | EApp f children => D.slots_fit db f (S (length children))
      | ELit _ => True
      end) full ->
    table_represents full (snd (build_nodes full table_empty db))
      (fst (build_nodes full table_empty db)) /\
    length (table_list (fst (build_nodes full table_empty db))) = length full.
  Proof.
    intros ds full db Hwf Hkind Htyped Hslots.
    set (P := fun rest t current => exists prefix,
      full = prefix ++ rest /\ length prefix = length (table_list t) /\
      table_represents full current t).
    assert (Hframe : P [] (fst (build_nodes full table_empty db))
      (snd (build_nodes full table_empty db))).
    { apply (build_nodes_frame_ready ds P) with (ns := full) (t := table_empty) (db := db).
      - intros n rest t current Hwf' Hkind' Hvalid Hallocated Htyped' Hslots'
          [prefix [Hfull [Hlength Htable]]]. cbv zeta.
        exists (prefix ++ [n]). split.
        + now rewrite <- app_assoc.
        + split.
          * rewrite table_push_list, !length_app. cbn [length]. now rewrite Hlength.
          * apply Forall_cons_iff in Hslots'. destruct Hslots' as [Hslot Hslots'].
            exact (table_represents_step ds full prefix n rest t current Hfull Hlength
              Hwf' Hkind' Hvalid Hallocated Htyped' Hslot Htable).
      - exact Hwf.
      - exact Hkind.
      - apply table_empty_valid.
      - constructor.
      - exact Htyped.
      - exact Hslots.
      - exists []. split; [reflexivity |]. split; [reflexivity |].
        intros j e Hbound Hunfold. cbn in Hbound. lia. }
    destruct Hframe as [prefix [Hfull [Hlength Htable]]].
    split; [exact Htable |]. rewrite app_nil_r in Hfull. subst full. symmetry. exact Hlength.
  Qed.

  Lemma add_expr_represents : forall ds e db t, D.wf db -> expr_ok ds db e ->
    unfolds_expr (expr_nodes V.t e) (expr_root V.t e) t ->
    represents (D.view (snd (add_expr e db))) (Id (fst (add_expr e db))) t.
  Proof.
    intros ds [ns root_index] db expression Hwf [Hexpr [Hkind Hslots]] Hunfold.
    pose proof (expr_nodes_typed V.t ds (FExpr V.t ns root_index) Hexpr) as Htyped.
    destruct (build_nodes_represents ds ns db Hwf Hkind Htyped Hslots) as [Hreps Hlength].
    pose proof (build_nodes_shape ns table_empty db (table_empty_valid (cell V.t))) as Hshape.
    unfold add_expr. destruct (build_nodes ns table_empty db) as [t final] eqn:Hresult.
    cbn [fst snd] in Hreps, Hlength, Hshape.
    destruct Hshape as [Hvalid Hsorts].
    change (map cell_sort (table_list t) = map enode_sort ns) in Hsorts.
    destruct Hexpr as [[f [children Hroot]] Hnodes].
    cbn [expr_nodes expr_root] in Hroot, Hunfold.
    assert (Hbound : root_index < length (table_list t)).
    { rewrite Hlength. apply nth_error_Some. rewrite Hroot. discriminate. }
    assert (Hroot_sort : nth_error (map cell_sort (table_list t)) root_index = Some SId).
    { rewrite Hsorts, nth_error_map, Hroot. reflexivity. }
    specialize (Hreps root_index expression Hbound Hunfold).
    rewrite nth_error_map in Hroot_sort.
    destruct (nth_error (table_list t) root_index) as [[i |v] |] eqn:Hcell;
      try discriminate Hroot_sort.
    rewrite (table_get_list _ (Id 1%positive) root_index t Hvalid), Hcell in Hreps |- *.
    exact Hreps.
  Qed.

  (** Every returned input class represents its input after the complete ordered input fold. *)
  Lemma inputs_represented : forall ds es db n e c t, D.wf db ->
    view_sorted (lookup_sorts ds) (D.view db) -> Forall (expr_ok ds db) es ->
    nth_error es n = Some e -> nth_error (fst (add_inputs es db)) n = Some c ->
    unfolds_expr (expr_nodes V.t e) (expr_root V.t e) t ->
    represents (D.view (snd (add_inputs es db))) (Id c) t.
  Proof.
    intros ds es. induction es as [| head rest IH];
      intros db n e c expression Hwf Hsorted Hexprs Hnth Hclass Hunfold;
      [destruct n; discriminate |].
    apply Forall_cons_iff in Hexprs. destruct Hexprs as [Hhead Hrest].
    destruct (add_expr_properties ds head db Hwf Hhead Hsorted)
      as [Hwf' [Hsorted' [Hkind [Hslots Hgrowth]]]].
    assert (Hrest' : Forall (expr_ok ds (snd (add_expr head db))) rest).
    { eapply Forall_impl; [| exact Hrest]. intros x Hx.
      exact (expr_ok_layout ds db (snd (add_expr head db)) x Hkind Hslots Hx). }
    cbn [add_inputs] in Hclass |- *.
    destruct (add_expr head db) as [i next] eqn:Hhead_result.
    cbn [snd] in Hwf', Hsorted', Hkind, Hslots, Hgrowth, Hrest'.
    destruct (add_inputs rest next) as [cs final] eqn:Hrest_result.
    cbn [fst snd] in Hclass |- *. destruct n as [| n].
    - cbn [nth_error] in Hnth, Hclass. inversion Hnth; inversion Hclass; subst e c.
      pose proof (add_expr_represents ds head db expression Hwf Hhead Hunfold)
        as Hrep. rewrite Hhead_result in Hrep. cbn [fst snd] in Hrep.
      destruct (add_inputs_properties ds rest next Hwf' Hsorted' Hrest')
        as [Hfinal [Hsort_final [Hkind_final [Hslots_final [Hids [Hrows Hsame]]]]]].
      rewrite Hrest_result in Hrows, Hsame. cbn [snd] in Hrows, Hsame.
      exact (represents_mono _ _ _ _ Hrows Hsame Hrep).
    - cbn [nth_error] in Hnth, Hclass.
      assert (Hclass' : nth_error (fst (add_inputs rest next)) n = Some c).
      { now rewrite Hrest_result. }
      pose proof (IH next n e c expression Hwf' Hsorted' Hrest' Hnth Hclass' Hunfold)
        as Hrep. now rewrite Hrest_result in Hrep.
  Qed.

  (** Engine growth preserves representation through row and identifier canonicalization. *)
  Lemma represents_grows : forall db db' c e, D.wf db' -> E.grows db db' ->
    represents (D.view db) c e -> represents (D.view db') c e.
  Proof.
    intros db db' c e Hwf [Hsame Hrows] Hrep.
    induction Hrep as [v | f k i j args Hrow Heq Hargs IHargs]; [constructor |].
    assert (Hcanonical : Forall2 (represents (D.view db')) (map (D.canon db') k) args).
    { clear Hrow Heq. induction IHargs as [| c e cs es Hr Hhead Htail Hall IH]; cbn [map].
      - constructor.
      - constructor; [now apply canon_represents | exact IH]. }
    destruct (Hrows f k (Some (Id j)) Hrow) as [output [Hrow' Hout]].
    destruct output as [[j' | v] |]; cbn [D.out_le option_map D.canon cell_le] in Hout;
      try contradiction.
    eapply rep_app; [exact Hrow' | | exact Hcanonical].
    apply (proj2 (D.same_repr db' i j' Hwf)).
    transitivity (D.repr db' j).
    - apply (proj1 (D.same_repr db' i j Hwf)). now apply Hsame.
    - apply (proj1 (D.same_repr db' (D.repr db' j) j' Hwf)) in Hout.
      now rewrite (D.repr_idem db' j Hwf) in Hout.
  Qed.

  (** Accepted inputs load into a well-formed database of the planned program. *)
  Lemma inputs_loaded : forall ds rws ans es, front_ok ds rws ans es ->
    let p := C.compile ds rws ans in
    let cp := E.plan p in
    D.wf (inputs_db es (E.load p cp)) /\ E.loaded p cp (inputs_db es (E.load p cp)).
  Proof.
    intros ds rws ans es [Hrules Hexprs]. cbv zeta.
    set (p := C.compile ds rws ans). set (cp := E.plan p).
    assert (Hdecls : decls V.t p = ds) by apply C.compile_program.
    assert (Hplan : E.plans_ok p cp).
    { apply E.plan_checked. now apply C.compile_sorted. }
    destruct (load_properties p cp) as [Hwf Hloaded].
    destruct Hloaded as [Hkind [Hslots Hsorted]].
    assert (Hsorted' : view_sorted (lookup_sorts ds) (D.view (E.load p cp))).
    { unfold program_sorts in Hsorted. now rewrite Hdecls in Hsorted. }
    assert (Hinputs : Forall (expr_ok ds (E.load p cp)) es).
    { eapply Forall_impl; [| exact Hexprs]. intros e Hexpr.
      eapply loaded_expr_ok; [exact Hdecls | exact Hplan | | exact Hexpr].
      split; [exact Hkind |]. split; assumption. }
    destruct (add_inputs_properties ds es (E.load p cp) Hwf Hsorted' Hinputs)
      as [Hwf' [Hsorted_final [Hkind_final [Hslots_final Hgrowth]]]].
    rewrite <- add_inputs_db. split; [exact Hwf' |]. unfold E.loaded. split.
    - intro f. now rewrite Hkind_final.
    - split; [now rewrite Hslots_final |].
      unfold program_sorts. now rewrite Hdecls.
  Qed.

  (** An accepted result is precisely the run on the loaded input fold. *)
  Lemma saturate_execution : forall ds rws ans lim es st db cs,
    saturate ds rws ans lim es = inr (st, db, cs) ->
    let p := C.compile ds rws ans in
    let cp := E.plan p in
    exists initial, front_ok ds rws ans es /\ E.plans_ok p cp /\ D.wf initial /\
      E.loaded p cp initial /\ add_inputs es (E.load p cp) = (cs, initial) /\
      E.run p cp lim initial = (st, db).
  Proof.
    intros ds rws ans lim es st db cs Hresult. unfold saturate in Hresult.
    destruct (check_front ds rws ans es) as [err |] eqn:Hcheck; [discriminate |].
    pose proof (proj1 (check_front_spec ds rws ans es) Hcheck) as Hfront.
    destruct (add_inputs es (E.load (C.compile ds rws ans)
      (E.plan (C.compile ds rws ans)))) as [ids initial] eqn:Hinputs.
    destruct (E.run (C.compile ds rws ans) (E.plan (C.compile ds rws ans)) lim initial)
      as [status final] eqn:Hrun.
    inversion Hresult; subst ids status final; clear Hresult.
    pose proof (inputs_loaded ds rws ans es Hfront) as Hloaded.
    cbv zeta in Hloaded.
    rewrite <- add_inputs_db, Hinputs in Hloaded. cbn in Hloaded.
    exists initial. split; [exact Hfront |]. split.
    - apply E.plan_checked. apply C.compile_sorted. exact (proj1 Hfront).
    - destruct Hloaded as [Hwf Hloaded].
      split; [exact Hwf |]. split; [exact Hloaded |]. split; assumption.
  Qed.

  Lemma saturate_wf : forall ds rws ans lim es st db cs,
    saturate ds rws ans lim es = inr (st, db, cs) ->
    D.wf db /\ D.canonical db /\ (forall f, kind (D.view db) f = lookup_kind ds f) /\
    view_sorted (lookup_sorts ds) (D.view db) /\
    D.slots db = Egglog.Syntax.slots V.t (E.plan (C.compile ds rws ans)).
  Proof.
    intros ds rws ans lim es st db cs Hresult.
    destruct (saturate_execution ds rws ans lim es st db cs Hresult)
      as [initial [Hfront [Hplan [Hwf [Hloaded [Hinputs Hrun]]]]]].
    pose proof (E.run_wf _ _ lim initial Hplan Hwf Hloaded) as Hfinal.
    rewrite Hrun in Hfinal. cbn in Hfinal.
    destruct Hfinal as [Hwf' [Hcanonical [Hkinds [Hslots Hsorted]]]].
    split; [exact Hwf' |]. split; [exact Hcanonical |].
    destruct (C.compile_program ds rws ans) as [Hdecls Hrules].
    split.
    - intro f. rewrite Hkinds. unfold program_kind. now rewrite Hdecls.
    - split; [| exact Hslots].
      unfold program_sorts in Hsorted. now rewrite Hdecls in Hsorted.
  Qed.

  Lemma saturate_represents : forall ds rws ans lim es st db cs n e c t,
    saturate ds rws ans lim es = inr (st, db, cs) ->
    nth_error es n = Some e -> nth_error cs n = Some c ->
    unfolds_expr (expr_nodes V.t e) (expr_root V.t e) t ->
    represents (D.view db) (Id c) t.
  Proof.
    intros ds rws ans lim es st db cs n e c expression Hresult Hnth Hclass Hunfold.
    destruct (saturate_execution ds rws ans lim es st db cs Hresult)
      as [initial [Hfront [Hplan [Hwf [Hloaded [Hinputs Hrun]]]]]].
    set (p := C.compile ds rws ans) in *.
    set (cp := E.plan p) in *.
    assert (Hdecls : decls V.t p = ds) by apply C.compile_program.
    destruct (load_properties p cp) as [Hwf_load Hloaded_load].
    assert (Hsorted_load : view_sorted (lookup_sorts ds) (D.view (E.load p cp))).
    { destruct Hloaded_load as [Hkind_load [Hslots_load Hsort]].
      unfold program_sorts in Hsort. now rewrite Hdecls in Hsort. }
    assert (Hexprs : Forall (expr_ok ds (E.load p cp)) es).
    { eapply Forall_impl; [| exact (proj2 Hfront)]. intros x Hx.
      exact (loaded_expr_ok p cp ds (E.load p cp) x Hdecls Hplan Hloaded_load Hx). }
    assert (Hclass' : nth_error (fst (add_inputs es (E.load p cp))) n = Some c).
    { now rewrite Hinputs. }
    pose proof (inputs_represented ds es (E.load p cp) n e c expression Hwf_load
      Hsorted_load Hexprs Hnth Hclass' Hunfold) as Hrep.
    rewrite Hinputs in Hrep. cbn [snd] in Hrep.
    pose proof (E.run_grows p cp lim initial Hplan Hwf Hloaded) as Hgrowth.
    pose proof (E.run_wf p cp lim initial Hplan Hwf Hloaded) as Hfinal.
    rewrite Hrun in Hgrowth, Hfinal. cbn [snd] in Hgrowth, Hfinal.
    exact (represents_grows initial db (Id c) expression (proj1 Hfinal) Hgrowth Hrep).
  Qed.

  (** Every accepted saturation outcome satisfies each model of its front-end rules. *)
  Lemma saturate_sat : forall (M : model (V := V.t)) ds rws ans lim es st db cs,
    model_ok M ds rws ans -> saturate ds rws ans lim es = inr (st, db, cs) ->
    exists nu, sat V.merge M nu (D.view db).
  Proof.
    intros M ds rws ans lim es st db cs [Hrewrites [Hanalyses Hmerge]] Hresult.
    destruct (saturate_execution ds rws ans lim es st db cs Hresult)
      as [initial [Hfront [Hplan [Hwf [Hloaded [Hinputs Hrun]]]]]].
    destruct (inputs_sat M ds rws ans es Hfront Hmerge) as [nu Hsat].
    rewrite Hinputs in Hsat. cbn [snd] in Hsat.
    pose proof (C.compile_valid M ds rws ans (proj1 Hfront) Hrewrites Hanalyses Hmerge)
      as Hvalid.
    destruct (E.run_sat _ _ lim initial M nu Hplan Hwf Hloaded Hvalid Hsat)
      as [nu' [Hstable Hsat']].
    rewrite Hrun in Hsat'. now exists nu'.
  Qed.

  Lemma saturate_sound : forall (M : model (V := V.t)) ds rws ans lim es st db cs
      i j e1 e2,
    model_ok M ds rws ans -> saturate ds rws ans lim es = inr (st, db, cs) ->
    represents (D.view db) (Id i) e1 -> represents (D.view db) (Id j) e2 ->
    same (D.view db) i j -> denote M e1 = denote M e2.
  Proof.
    intros M ds rws ans lim es st db cs i j e1 e2 Hmodel Hresult Hfirst Hsecond Heq.
    destruct (saturate_sat M ds rws ans lim es st db cs Hmodel Hresult) as [nu Hsat].
    rewrite <- (represents_den V.merge M nu (D.view db) (Id i) e1 Hsat Hfirst).
    rewrite <- (represents_den V.merge M nu (D.view db) (Id j) e2 Hsat Hsecond).
    cbn [den]. f_equal. exact (sat_same V.merge M nu (D.view db) i j Hsat Heq).
  Qed.

  Lemma saturate_facts : forall (M : model (V := V.t)) ds rws ans lim es st db cs
      f k o ts,
    model_ok M ds rws ans -> saturate ds rws ans lim es = inr (st, db, cs) ->
    row (D.view db) f k o -> Forall2 (represents (D.view db)) k ts ->
    match lookup_kind ds f, o with
    | Some ORel, None => rel M f (map (denote M) ts)
    | Some (OLat _), Some (Val v) => lat M f (map (denote M) ts) v
    | Some OId, Some (Id i) => forall e, represents (D.view db) (Id i) e ->
        inl (con M f (map (denote M) ts)) = denote M e
    | _, _ => False
    end.
  Proof.
    intros M ds rws ans lim es st db cs f k o ts Hmodel Hresult Hrow Hargs.
    destruct (saturate_sat M ds rws ans lim es st db cs Hmodel Hresult) as [nu Hsat].
    destruct (saturate_wf ds rws ans lim es st db cs Hresult)
      as [Hwf [Hcanonical [Hkind Hrest]]].
    assert (Hden : map (den nu) k = map (denote M) ts).
    { clear Hrow. induction Hargs as [| c e cells exprs Hrep Hargs IH]; cbn [map].
      - reflexivity.
      - rewrite (represents_den V.merge M nu (D.view db) c e Hsat Hrep), IH.
        reflexivity. }
    pose proof (proj1 Hsat f k o Hrow) as Hholds.
    unfold holds in Hholds. rewrite Hkind, Hden in Hholds.
    destruct (lookup_kind ds f) as [[| |m] |]; destruct o as [[i |v] |];
      cbn in Hholds |- *; try contradiction; try assumption.
    intros e Hrep.
    rewrite <- (represents_den V.merge M nu (D.view db) (Id i) e Hsat Hrep).
    cbn [den]. now rewrite Hholds.
  Qed.

  (** Canonical database rows provide the compiler's canonical view. *)
  Lemma canonical_view_db : forall db, D.wf db -> D.canonical db ->
    C.canonical_view (D.view db).
  Proof.
    intros db Hwf Hcanonical. unfold C.canonical_view. split.
    - intro i. apply (proj2 (D.same_repr db i i Hwf)). reflexivity.
    - split.
      + intros i j Hsame. apply (proj2 (D.same_repr db j i Hwf)).
        symmetry. exact (proj1 (D.same_repr db i j Hwf) Hsame).
      + split.
        * intros i j k Hij Hjk. apply (proj2 (D.same_repr db i k Hwf)).
          transitivity (D.repr db j).
          -- exact (proj1 (D.same_repr db i j Hwf) Hij).
          -- exact (proj1 (D.same_repr db j k Hwf) Hjk).
        * split.
          -- intros f k o1 o2 Hrow1 Hrow2.
             exact (D.row_functional db f k o1 o2 Hwf Hrow1 Hrow2).
          -- intros f k o f' k' o' i j Hrow Hrow' Hin Hin' Hsame.
             pose proof (proj1 (D.same_repr db i j Hwf) Hsame) as Heq.
             rewrite (Hcanonical f k o Hrow i Hin),
               (Hcanonical f' k' o' Hrow' j Hin') in Heq. exact Heq.
  Qed.


  Lemma ematch_complete : forall ds db rw g tau c e, D.wf db -> D.canonical db ->
    rewrite_ok (lookup_sorts ds) (lookup_kind ds) rw g ->
    C.instantiates tau (lhs V.t rw) e -> represents (D.view db) (Id c) e ->
    cond_in_db db tau (cond V.t rw) -> exists s,
      matches V.prim (D.view db) (C.flatten_lhs rw) s /\
      C.represents_on g (D.view db) tau s /\
      s (C.root_var rw) = Some (Id (D.repr db c)).
  Proof.
    intros ds db rw g tau c e Hwf Hcanonical Hrw Hinst Hrep Hcond.
    destruct (C.flatten_complete ds (D.view db) rw g tau c e Hrw
      (canonical_view_db db Hwf Hcanonical) Hinst Hrep Hcond)
      as [s [j [Hmatch [Hon [Hroot [Hsame [f [k Hrow]]]]]]]].
    assert (Hrepr : D.repr db j = j).
    { apply (Hcanonical f k (Some (Id j)) Hrow j).
      apply in_or_app. right. now left. }
    pose proof (proj1 (D.same_repr db c j Hwf) Hsame) as Heq.
    rewrite Hrepr in Heq. exists s. split; [exact Hmatch |].
    split; [exact Hon |]. now rewrite Heq.
  Qed.

  (** Engine closure realizes every represented instance of a compiled rewrite. *)
  Lemma closed_represents : forall ds rws ans db rw g tau c l r,
    D.wf db -> D.canonical db -> (forall f, kind (D.view db) f = lookup_kind ds f) ->
    view_sorted (lookup_sorts ds) (D.view db) ->
    closed V.prim V.merge (C.compile ds rws ans) (D.view db) ->
    In rw rws -> rewrite_ok (lookup_sorts ds) (lookup_kind ds) rw g ->
    C.instantiates tau (lhs V.t rw) l -> C.instantiates tau (rhs V.t rw) r ->
    represents (D.view db) (Id c) l -> cond_in_db db tau (cond V.t rw) ->
    represents (D.view db) (Id c) r.
  Proof.
    intros ds rws ans db rw g tau c l r Hwf Hcanonical Hkind Hsort Hclosed Hin Hrw
      Hleft Hright Hrep Hcond.
    pose proof (canonical_view_db db Hwf Hcanonical) as Hview.
    destruct (C.flatten_complete ds (D.view db) rw g tau c l Hrw Hview Hleft Hrep Hcond)
      as [s [j [Hmatch [Hon [Hroot [Hsame Hrow]]]]]].
    assert (Hpresent : present V.prim V.merge (D.view db) s (actions V.t (C.compile_rule rw))).
    { apply (Hclosed (C.compile_rule rw) s).
      - rewrite (proj2 (C.compile_program ds rws ans)).
        apply in_or_app. left. apply in_map. exact Hin.
      - rewrite C.compile_query. exact Hmatch. }
    apply (represents_same db c j r Hwf Hsame).
    exact (C.present_represents ds (D.view db) rw g s tau j r Hrw Hsort Hkind Hview
      Hmatch Hroot Hon Hright Hpresent).
  Qed.

  Lemma saturated_closed : forall ds rws ans lim es db cs rw tau c l r,
    saturate ds rws ans lim es = inr (Saturated, db, cs) -> In rw rws ->
    C.instantiates tau (lhs V.t rw) l -> C.instantiates tau (rhs V.t rw) r ->
    represents (D.view db) (Id c) l -> cond_in_db db tau (cond V.t rw) ->
    represents (D.view db) (Id c) r.
  Proof.
    intros ds rws ans lim es db cs rw tau c l r Hresult Hin Hleft Hright Hrep Hcond.
    destruct (saturate_execution ds rws ans lim es Saturated db cs Hresult)
      as [initial [Hfront [Hplan [Hwf [Hloaded [Hinputs Hrun]]]]]].
    pose proof (E.run_closed _ _ lim initial db Hplan Hwf Hloaded Hrun) as Hclosed.
    destruct (saturate_wf ds rws ans lim es Saturated db cs Hresult)
      as [Hfinal [Hcanonical [Hkinds [Hsorted Hslots]]]].
    destruct Hfront as [[Hrewrites Hanalyses] Hexprs].
    apply Forall_forall with (x := rw) in Hrewrites; [| exact Hin].
    destruct Hrewrites as [g Hrw].
    exact (closed_represents ds rws ans db rw g tau c l r Hfinal Hcanonical Hkinds Hsorted
      Hclosed Hin Hrw Hleft Hright Hrep Hcond).
  Qed.

  Lemma saturated_analyses : forall ds rws ans lim es db cs r s,
    saturate ds rws ans lim es = inr (Saturated, db, cs) -> In r ans ->
    matches V.prim (D.view db) (query V.t r) s ->
    present V.prim V.merge (D.view db) s (actions V.t r).
  Proof.
    intros ds rws ans lim es db cs r s Hresult Hin Hmatch.
    destruct (saturate_execution ds rws ans lim es Saturated db cs Hresult)
      as [initial [Hfront [Hplan [Hwf [Hloaded [Hinputs Hrun]]]]]].
    pose proof (E.run_closed _ _ lim initial db Hplan Hwf Hloaded Hrun) as Hclosed.
    apply (Hclosed r s); [| exact Hmatch].
    rewrite (proj2 (C.compile_program ds rws ans)). apply in_or_app. now right.
  Qed.

  Lemma saturate_limits : forall ds rws ans lim es db cs,
    saturate ds rws ans lim es = inr (IdLimit, db, cs) -> (D.ids db > max_ids lim)%N.
  Proof.
    intros ds rws ans lim es db cs Hresult.
    destruct (saturate_execution ds rws ans lim es IdLimit db cs Hresult)
      as [initial [Hfront [Hplan [Hwf [Hloaded [Hinputs Hrun]]]]]].
    pose proof (E.run_limits (C.compile ds rws ans) (E.plan (C.compile ds rws ans))
      lim initial) as Hlimit.
    rewrite Hrun in Hlimit. cbn in Hlimit. now apply Hlimit.
  Qed.
End Saturate.

Module SaturateT (V : VALUE_T) (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I)
    (E : RUN_T V I J D) (C : COMPILE_T V) <: SATURATE_ALL V I J D E C.
  Include Saturate V I J D E C.
  TimeFun check_front.
  TimeFun add_node.
  TimeFun build_nodes.
  TimeFun add_expr.
  TimeFun add_inputs.
  TimeFun saturate.
  Definition c_sat : N := (2 * 4096 + 4 * (8 * 1024) * (D.c_db + 1))%N.
  Fixpoint T_inputs (es : list (fexpr V.t)) (db : D.t) : N :=
    match es with
    | [] => 1%N
    | e :: rest => (T_add_expr e db + 1 + T_inputs rest (snd (add_expr e db)))%N
    end.
  (** Adding a node pays for one database make and a fixed wrapper cost. *)
  Lemma T_add_node_overhead : forall node cells db,
    (T_add_node node cells db <= match node with
     | EApp f _ => D.T_make f cells db + 16
     | ELit _ => 16
     end)%N.
  Proof.
    intros [f children | v] cells db; time_unfold T_add_node; time_cbn; lia.
  Qed.

  (** The paired input fold pays a fixed factor of the specified input cost. *)
  Lemma T_add_inputs_overhead : forall es db, (T_add_inputs es db <= 16 * T_inputs es db)%N.
  Proof.
    induction es as [| e rest IH]; intro db.
    - time_unfold T_add_inputs. unfold T_inputs. time_cbn. lia.
    - time_unfold T_add_inputs. cbn [T_inputs].
      destruct (add_expr e db) as [i next] eqn:Hexpr.
      specialize (IH next). destruct (add_inputs rest next) as [cs final] eqn:Hrest.
      time_cbn. nia.
  Qed.

  (** The saturation wrapper pays for each invoked phase and a fixed amount of control work. *)
  Lemma T_saturate_overhead : forall ds rws ans lim es,
    let p := C.compile ds rws ans in
    let cp := E.plan p in
    (T_saturate ds rws ans lim es <= T_check_front ds rws ans es + 16 +
      match check_front ds rws ans es with
      | Some _ => 0
      | None => C.T_compile ds rws ans + E.T_plan p + E.T_load p cp +
          T_add_inputs es (E.load p cp) +
          E.T_run p cp lim (snd (add_inputs es (E.load p cp)))
      end)%N.
  Proof.
    intros ds rws ans lim es. cbv zeta. time_unfold T_saturate.
    destruct (check_front ds rws ans es) as [err |] eqn:Hcheck; [time_cbn; lia |].
    destruct (add_inputs es (E.load (C.compile ds rws ans)
      (E.plan (C.compile ds rws ans)))) as [cs initial] eqn:Hinputs.
    destruct (E.run (C.compile ds rws ans) (E.plan (C.compile ds rws ans)) lim initial)
      as [st final] eqn:Hrun.
    time_cbn. lia.
  Qed.

  (** An amortized inequality remains valid when its positive spending unit increases. *)
  Lemma amort_scale : forall cost r u before after extra,
    (0 < r <= u)%N -> (cost + r * after <= r * (extra + before))%N ->
    (cost + u * after <= u * (extra + before))%N.
  Proof.
    intros cost r u before after extra [Hr Hu] Hcost.
    assert (Hcredit : (after <= extra + before)%N) by nia. nia.
  Qed.

  (** Every database has a positive spending unit. *)
  Lemma unit_positive : forall db, 1 <= D.unit db.
  Proof.
    intro db. unfold D.unit. nia.
  Qed.

  (** The common node budget is positive at every permitted spending unit. *)
  Lemma node_budget_positive : forall B U db width, D.unit db <= U -> 1 <= width ->
    (1 <= N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) *
      N.of_nat (D.num_slots db + 1) * N.of_nat width)%N.
  Proof.
    intros B U db width HU Hwidth.
    assert (Hu : (1 <= N.of_nat U)%N).
    { pose proof (unit_positive db). lia. }
    assert (Hl : (1 <= N.of_nat (N.to_nat (N.log2 B) + 1))%N) by
      lia.
    assert (Hs : (1 <= N.of_nat (D.num_slots db + 1))%N) by
      lia.
    assert (Hwidth' : (1 <= N.of_nat width)%N) by lia.
    pose proof (N.mul_le_mono 1 _ 1 _ Hu Hl) as Hul.
    pose proof (N.mul_le_mono 1 _ 1 _ Hul Hs) as Huls.
    exact (N.mul_le_mono 1 _ 1 _ Huls Hwidth').
  Qed.

  (** Node insertion transfers potential using a small portion of the public plan constant. *)
  Lemma add_node_amort_bound : forall B U node cells db, D.wf db ->
    (forall i, In (Id i) cells -> D.allocated db i) ->
    match node with
    | EApp f _ => kind (D.view db) f = Some OId /\ D.slots_fit db f (S (length cells))
    | ELit _ => cells = []
    end ->
    (D.ids (snd (add_node node cells db)) <= B)%N ->
    D.unit (snd (add_node node cells db)) <= U ->
    (T_add_node node cells db + N.of_nat U * D.potential B (snd (add_node node cells db)) <=
      32 * (D.c_db + 1) * N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) *
        N.of_nat (D.num_slots db + 1) * N.of_nat ((length cells + 2) * (length cells + 2)) +
      N.of_nat U * D.potential B db)%N.
  Proof.
    intros B U [f children | v] cells db Hwf Hallocated Hnode Hids HU.
    - destruct Hnode as [Hkind Hfits].
      pose proof (D.T_make_amort B f cells db Hwf Hfits) as Hmake_cost.
      pose proof (T_add_node_overhead (EApp f children) cells db) as Hwrapper.
      pose proof (D.layout_make f cells db Hwf) as Hlayout.
      cbn [add_node] in Hids, HU |- *.
      destruct (D.make f cells db) as [i next] eqn:Hmake.
      cbn [fst snd] in Hids, HU, Hmake_cost, Hlayout |- *.
      specialize (Hmake_cost Hids).
      assert (Hr : (0 < N.of_nat (D.unit next) <= N.of_nat U)%N).
      { split; [pose proof (unit_positive next); lia | lia]. }
      pose proof (amort_scale _ _ _ _ _ _ Hr Hmake_cost) as Hscaled.
      assert (Hslots : (N.of_nat (D.slots_of db f + 1) <=
        N.of_nat (D.num_slots db + 1))%N).
      { unfold D.slots_of, D.num_slots.
        pose proof (filter_length_le (fun s => Pos.eqb (fst s) f) (D.slots db)). lia. }
      assert (Hextra : (D.c_db * N.of_nat ((length cells + 2) * (length cells + 2)) *
        N.of_nat (D.slots_of db f + 1) * N.of_nat (N.to_nat (N.log2 B) + 1) <=
        D.c_db * N.of_nat ((length cells + 2) * (length cells + 2)) *
        N.of_nat (D.num_slots db + 1) * N.of_nat (N.to_nat (N.log2 B) + 1))%N).
      { apply N.mul_le_mono_r. now apply N.mul_le_mono_l. }
      assert (Hbudget : (N.of_nat U *
        (D.c_db * N.of_nat ((length cells + 2) * (length cells + 2)) *
          N.of_nat (D.slots_of db f + 1) * N.of_nat (N.to_nat (N.log2 B) + 1) +
          D.potential B db) <= N.of_nat U *
        (D.c_db * N.of_nat ((length cells + 2) * (length cells + 2)) *
          N.of_nat (D.num_slots db + 1) * N.of_nat (N.to_nat (N.log2 B) + 1) +
          D.potential B db))%N).
      { apply N.mul_le_mono_l. lia. }
      set (q := (N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) *
        N.of_nat (D.num_slots db + 1) *
        N.of_nat ((length cells + 2) * (length cells + 2)))%N).
      assert (Hq : (1 <= q)%N).
      { unfold q. apply node_budget_positive; [| nia].
        destruct Hlayout as [Hkind' [Hslots' Hrest]].
        pose proof (D.unit_mono_make f cells db Hwf) as Hmono.
        rewrite Hmake in Hmono. cbn [snd] in Hmono. lia. }
      assert (Hscaled' : (D.T_make f cells db + N.of_nat U * D.potential B next <=
        D.c_db * q + N.of_nat U * D.potential B db)%N).
      { eapply N.le_trans; [exact Hscaled |].
        eapply N.le_trans; [exact Hbudget |]. unfold q. ring_simplify. reflexivity. }
      replace (32 * (D.c_db + 1) * N.of_nat U *
        N.of_nat (N.to_nat (N.log2 B) + 1) * N.of_nat (D.num_slots db + 1) *
        N.of_nat ((length cells + 2) * (length cells + 2)))%N
        with (32 * (D.c_db + 1) * q)%N by (unfold q; ring).
      change (T_add_node (EApp f children) cells db <= D.T_make f cells db + 16)%N
        in Hwrapper. nia.
    - subst cells. cbn [add_node fst snd] in HU |- *.
      pose proof (T_add_node_overhead (ELit v) [] db) as Hwrapper.
      pose proof (node_budget_positive B U db ((length (@nil (cell V.t)) + 2) *
        (length (@nil (cell V.t)) + 2)) HU ltac:(cbn; lia)) as Hpositive.
      set (q := (N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) *
        N.of_nat (D.num_slots db + 1) *
        N.of_nat ((length (@nil (cell V.t)) + 2) * (length (@nil (cell V.t)) + 2)))%N) in *.
      replace (32 * (D.c_db + 1) * N.of_nat U *
        N.of_nat (N.to_nat (N.log2 B) + 1) * N.of_nat (D.num_slots db + 1) *
        N.of_nat ((length (@nil (cell V.t)) + 2) * (length (@nil (cell V.t)) + 2)))%N
        with (32 * (D.c_db + 1) * q)%N by (unfold q; ring).
      change (T_add_node (ELit v) [] db <= 16)%N in Hwrapper. nia.
  Qed.

  Lemma T_check_front_le : forall ds rws ans es,
    (T_check_front ds rws ans es <= c_sat * N.of_nat (front_size ds rws ans es + 1))%N.
  Proof.
    intros ds rws ans es. pose proof (front_check_clock V.t ds rws ans es).
    time_unfold @T_check_front; time_simpl. unfold c_sat. nia.
  Qed.


  Lemma T_saturate_le : forall ds rws ans lim es,
    let p := C.compile ds rws ans in
    let cp := E.plan p in
    (T_saturate ds rws ans lim es <= T_check_front ds rws ans es + c_sat +
      match check_front ds rws ans es with
      | Some _ => 0
      | None => C.T_compile ds rws ans + E.T_plan p + E.T_load p cp +
          c_sat * T_inputs es (E.load p cp) +
          E.T_run p cp lim (inputs_db es (E.load p cp))
      end)%N.
  Proof.
    intros ds rws ans lim es. cbv zeta.
    pose proof (T_saturate_overhead ds rws ans lim es) as Hcost. cbv zeta in Hcost.
    destruct (check_front ds rws ans es) as [err |] eqn:Hcheck.
    - unfold c_sat. nia.
    - pose proof (T_add_inputs_overhead es
        (E.load (C.compile ds rws ans) (E.plan (C.compile ds rws ans)))) as Hinputs.
      rewrite add_inputs_db in Hcost. unfold c_sat. nia.
  Qed.

  Definition k_sat : N := (8 * 1024 * (D.c_db + 1))%N.
  Definition node_args (n : enode V.t) (cs : list (cell V.t)) : list (cell V.t) :=
    match n with
    | EApp _ ch => map (fun j => nth j cs (Id 1%positive)) ch
    | ELit _ => []
    end.
  (** The cells and the database after adding nodes in order. *)
  Fixpoint add_nodes (ns : list (enode V.t)) (cs : list (cell V.t)) (db : D.t)
      : list (cell V.t) * D.t :=
    match ns with
    | [] => (cs, db)
    | n :: rest =>
        add_nodes rest (cs ++ [fst (add_node n (node_args n cs) db)])
          (snd (add_node n (node_args n cs) db))
    end.
  Fixpoint T_add_nodes (ns : list (enode V.t)) (cs : list (cell V.t)) (db : D.t) : N :=
    match ns with
    | [] => 0%N
    | n :: rest =>
        (T_add_node n (node_args n cs) db +
          T_add_nodes rest (cs ++ [fst (add_node n (node_args n cs) db)])
            (snd (add_node n (node_args n cs) db)))%N
    end.
  (** Adding a node never reduces the database's unit budget. *)
  Lemma add_node_unit : forall node cells db, D.wf db ->
    D.unit db <= D.unit (snd (add_node node cells db)).
  Proof.
    intros [f children | v] cells db Hwf; cbn [add_node].
    - pose proof (D.unit_mono_make f cells db Hwf) as Hunit.
      destruct (D.make f cells db). exact Hunit.
    - apply Nat.le_refl.
  Qed.

  Lemma F1_add_expr_step : forall ds node cells db, D.wf db ->
    view_sorted (lookup_sorts ds) (D.view db) ->
    (forall f, kind (D.view db) f = lookup_kind ds f) ->
    (forall i, In (Id i) cells -> D.allocated db i) ->
    match node with
    | EApp f _ => lookup_kind ds f = Some OId /\
        lookup_sorts ds f = Some (map cell_sort cells) /\ D.slots_fit db f (S (length cells))
    | ELit _ => cells = []
    end ->
    D.wf (snd (add_node node cells db)) /\
    view_sorted (lookup_sorts ds) (D.view (snd (add_node node cells db))) /\
    kind (D.view (snd (add_node node cells db))) = kind (D.view db) /\
    D.slots (snd (add_node node cells db)) = D.slots db /\
    (forall i, fst (add_node node cells db) = Id i ->
      D.allocated (snd (add_node node cells db)) i) /\
    cell_sort (fst (add_node node cells db)) = enode_sort node /\
    (D.ids db <= D.ids (snd (add_node node cells db)))%N /\
    D.unit db <= D.unit (snd (add_node node cells db)).
  Proof.
    intros ds node cells db Hwf Hsorted Hkind Hallocated Hnode.
    destruct (add_node_properties ds node cells db Hwf Hsorted Hkind Hallocated Hnode)
      as [Hwf' [Hsorted' [Hkind' [Hslots [Hnew [Hids Hgrowth]]]]]].
    split; [exact Hwf' |]. split; [exact Hsorted' |]. split; [exact Hkind' |].
    split; [exact Hslots |]. split; [exact Hnew |]. split; [apply add_node_sort |].
    split; [exact Hids |]. now apply add_node_unit.
  Qed.

  (** The well-typed node fold never reduces the database's unit budget. *)
  Lemma build_nodes_unit : forall ds ns t db, D.wf db ->
    view_sorted (lookup_sorts ds) (D.view db) ->
    (forall f, kind (D.view db) f = lookup_kind ds f) ->
    table_valid t -> table_allocated db t ->
    nodes_typed ds (map cell_sort (table_list t)) ns ->
    Forall (fun node => match node with
      | EApp f children => D.slots_fit db f (S (length children))
      | ELit _ => True
      end) ns ->
    D.unit db <= D.unit (snd (build_nodes ns t db)).
  Proof.
    intros ds ns t db Hwf Hsorted Hkind Hvalid Hallocated Htyped Hslots.
    apply (build_nodes_frame ds (fun _ _ next => D.unit db <= D.unit next))
      with (ns := ns) (t := t) (db := db); try assumption; [| apply Nat.le_refl].
    intros n rest cells_db current Hwf' Hsorted' Hkind' Hvalid' Hallocated' Htyped'
      Hslots' Hunit. cbv zeta.
    eapply Nat.le_trans; [exact Hunit |]. now apply add_node_unit.
  Qed.

  (** Adding an admissible expression never reduces the database's unit budget. *)
  Lemma add_expr_unit : forall ds e db, D.wf db -> expr_ok ds db e ->
    view_sorted (lookup_sorts ds) (D.view db) ->
    D.unit db <= D.unit (snd (add_expr e db)).
  Proof.
    intros ds [ns root_index] db Hwf [Hexpr [Hkind Hslots]] Hsorted.
    pose proof (expr_nodes_typed V.t ds (FExpr V.t ns root_index) Hexpr) as Htyped.
    assert (Hallocated : table_allocated db (@table_empty (cell V.t))) by constructor.
    pose proof (build_nodes_unit ds ns table_empty db Hwf Hsorted Hkind
      (table_empty_valid (cell V.t)) Hallocated Htyped Hslots) as Hunit.
    unfold add_expr. destruct (build_nodes ns table_empty db) as [t final].
    destruct (table_get (Id 1%positive) root_index t); exact Hunit.
  Qed.

  Lemma F2_add_expr_wf : forall ds e db, D.wf db -> expr_ok ds db e ->
    view_sorted (lookup_sorts ds) (D.view db) ->
    D.wf (snd (add_expr e db)) /\
    view_sorted (lookup_sorts ds) (D.view (snd (add_expr e db))) /\
    kind (D.view (snd (add_expr e db))) = kind (D.view db) /\
    D.slots (snd (add_expr e db)) = D.slots db /\
    D.allocated (snd (add_expr e db)) (fst (add_expr e db)) /\
    (D.ids db <= D.ids (snd (add_expr e db)))%N /\
    D.unit db <= D.unit (snd (add_expr e db)).
  Proof.
    intros ds e db Hwf Hexpr Hsorted.
    destruct (add_expr_properties ds e db Hwf Hexpr Hsorted)
      as [Hwf' [Hsorted' [Hkind [Hslots [Hroot [Hids Hgrowth]]]]]].
    split; [exact Hwf' |]. split; [exact Hsorted' |]. split; [exact Hkind |].
    split; [exact Hslots |]. split; [exact Hroot |]. split; [exact Hids |].
    exact (add_expr_unit ds e db Hwf Hexpr Hsorted).
  Qed.

  Lemma F3_represents_den : forall (M : model (V := V.t)) nu db c e,
    D.wf db -> sat V.merge M nu (D.view db) -> represents (D.view db) c e ->
    denote M e = den nu c.
  Proof.
    intros M nu db c e Hwf Hsat Hrep.
    symmetry. exact (represents_den V.merge M nu (D.view db) c e Hsat Hrep).
  Qed.

  Lemma F4_inputs_sat : forall (M : model (V := V.t)) ds rws ans es,
    front_ok ds rws ans es ->
    (forall f m k a b, lookup_kind ds f = Some (OLat m) ->
      lat M f k a -> lat M f k b -> lat M f k (V.merge m a b)) ->
    let p := C.compile ds rws ans in
    exists nu, sat V.merge M nu (D.view (snd (add_inputs es (E.load p (E.plan p))))).
  Proof.
    exact inputs_sat.
  Qed.

  Lemma F5_saturate_run : forall ds rws ans lim es out,
    saturate ds rws ans lim es = inr out ->
    let p := C.compile ds rws ans in
    let cp := E.plan p in
    exists initial, front_ok ds rws ans es /\ E.plans_ok p cp /\ D.wf initial /\
      E.loaded p cp initial /\ add_inputs es (E.load p cp) = (snd out, initial) /\
      E.run p cp lim initial = fst out.
  Proof.
    intros ds rws ans lim es [[st db] cs] Hresult.
    exact (saturate_execution ds rws ans lim es st db cs Hresult).
  Qed.

  Lemma F6_closed_represents : forall ds rws ans db rw g tau c l r,
    D.wf db -> D.canonical db -> (forall f, kind (D.view db) f = lookup_kind ds f) ->
    view_sorted (lookup_sorts ds) (D.view db) ->
    closed V.prim V.merge (C.compile ds rws ans) (D.view db) ->
    In rw rws -> rewrite_ok (lookup_sorts ds) (lookup_kind ds) rw g ->
    C.instantiates tau (lhs V.t rw) l -> C.instantiates tau (rhs V.t rw) r ->
    represents (D.view db) (Id c) l -> cond_in_db db tau (cond V.t rw) ->
    represents (D.view db) (Id c) r.
  Proof.
    exact closed_represents.
  Qed.

  Lemma F7_add_inputs : forall es db,
    snd (add_inputs es db) = inputs_db es db /\
    length (fst (add_inputs es db)) = length es /\
    (T_add_inputs es db <= k_sat * T_inputs es db)%N.
  Proof.
    intros es db. split; [apply add_inputs_db |]. split; [apply add_inputs_length |].
    pose proof (T_add_inputs_overhead es db) as Hcost. unfold k_sat. nia.
  Qed.

  Lemma F8_inputs_represented : forall ds es db n e c t, D.wf db ->
    view_sorted (lookup_sorts ds) (D.view db) -> Forall (expr_ok ds db) es ->
    nth_error es n = Some e -> nth_error (fst (add_inputs es db)) n = Some c ->
    unfolds_expr (expr_nodes V.t e) (expr_root V.t e) t ->
    represents (D.view (snd (add_inputs es db))) (Id c) t.
  Proof.
    exact inputs_represented.
  Qed.

  Lemma F9_canonical_view : forall db, D.wf db -> D.canonical db ->
    C.canonical_view (D.view db).
  Proof.
    exact canonical_view_db.
  Qed.

  Lemma T1_saturate_split : forall ds rws ans lim es,
    let p := C.compile ds rws ans in
    let cp := E.plan p in
    (T_saturate ds rws ans lim es <= T_check_front ds rws ans es + k_sat +
      match check_front ds rws ans es with
      | Some _ => 0
      | None => C.T_compile ds rws ans + E.T_plan p + E.T_load p cp +
          T_add_inputs es (E.load p cp) +
          E.T_run p cp lim (snd (add_inputs es (E.load p cp)))
      end)%N.
  Proof.
    intros ds rws ans lim es. cbv zeta.
    pose proof (T_saturate_overhead ds rws ans lim es) as Hcost. cbv zeta in Hcost.
    unfold k_sat. nia.
  Qed.

  Lemma T2_k_sat : (k_sat <= c_sat)%N.
  Proof.
    unfold k_sat, c_sat. nia.
  Qed.

  (** Adding a flat expression folds over its nodes in order and returns its root cell. *)
  (** The optimized node table computes the same ordered fold as the plan's lists. *)
  Lemma build_nodes_reference : forall ns t db, table_valid t ->
    add_nodes ns (table_list t) db =
      (table_list (fst (build_nodes ns t db)), snd (build_nodes ns t db)).
  Proof.
    induction ns as [| n rest IH]; intros t db Hvalid; [reflexivity |].
    assert (Hargs : node_args n (table_list t) = match n with
      | EApp _ children => map (fun j => table_get (Id 1%positive) j t) children
      | ELit _ => []
      end).
    { destruct n as [f children | v]; [| reflexivity]. cbn [node_args].
      apply map_ext. intro j. symmetry. now apply table_get_nth. }
    cbn [add_nodes build_nodes]. rewrite Hargs.
    destruct (add_node n
      (match n with
       | EApp _ children => map (fun j => table_get (Id 1%positive) j t) children
       | ELit _ => []
       end) db) as [c next] eqn:Hnode_result.
    cbn [fst snd]. rewrite <- table_push_list.
    apply IH. now apply table_push_valid.
  Qed.

  Lemma F10_add_expr_nodes : forall ds e db,
    expr_sorted (lookup_sorts ds) (lookup_kind ds) e ->
    snd (add_expr e db) = snd (add_nodes (expr_nodes V.t e) [] db) /\
    nth_error (fst (add_nodes (expr_nodes V.t e) [] db)) (expr_root V.t e) =
      Some (Id (fst (add_expr e db))).
  Proof.
    intros ds [ns root_index] db [[f [children Hroot]] Hnodes].
    pose proof (build_nodes_shape ns table_empty db (table_empty_valid (cell V.t)))
      as Hshape.
    change (table_valid (fst (build_nodes ns table_empty db)) /\
      map cell_sort (table_list (fst (build_nodes ns table_empty db))) = map enode_sort ns)
      in Hshape.
    pose proof (build_nodes_reference ns table_empty db (table_empty_valid (cell V.t)))
      as Hreference.
    change (add_nodes ns [] db =
      (table_list (fst (build_nodes ns table_empty db)), snd (build_nodes ns table_empty db)))
      in Hreference.
    unfold add_expr. destruct (build_nodes ns table_empty db) as [t final] eqn:Hresult.
    cbn [expr_nodes expr_root] in Hroot |- *.
    cbn [fst snd] in Hshape, Hreference. rewrite Hreference. cbn [fst snd].
    destruct Hshape as [Hvalid Hsorts].
    change (map cell_sort (table_list t) = map enode_sort ns) in Hsorts.
    assert (Hroot_sort : nth_error (map cell_sort (table_list t)) root_index = Some SId).
    { rewrite Hsorts, nth_error_map, Hroot. reflexivity. }
    rewrite nth_error_map in Hroot_sort.
    destruct (nth_error (table_list t) root_index) as [[i |v] |] eqn:Hcell;
      try discriminate Hroot_sort.
    rewrite table_get_list by exact Hvalid. rewrite Hcell. split; reflexivity.
  Qed.
  (** Unary table subtraction reads at most its first argument. *)
  Lemma table_sub_clock : forall n m, (T_table_sub n m <= N.of_nat (n + 1))%N.
  Proof.
    induction n as [| n IH]; intros [| m]; time_step.
  Qed.

  (** Table pushes pay for occasional copying from credit on the accumulated suffix. *)
  Lemma table_push_clock : forall A (x : A) t, table_valid t ->
    (T_table_push x t + 16 * N.of_nat (table_back_size (table_push x t)) <=
      32 + 16 * N.of_nat (table_back_size t))%N.
  Proof.
    intros A x [front back nf nb room] [Hfront [Hback Hroom]].
    cbn [table_front table_back table_front_size table_back_size table_room] in *.
    destruct room as [| room].
    - pose proof (Nat.T_add_le nf nb) as Hplus.
      pose proof (Datatypes.T_app_le front (rev_append (x :: back) [])) as Happ.
      pose proof (List.T_rev_append_le (x :: back) []) as Hreverse.
      time_unfold @T_table_push. time_simpl.
      unfold table_push. cbn [table_room table_front table_back table_front_size table_back_size].
      cbn [length] in Hreverse. rewrite Nat2N.inj_succ in Hreverse. lia.
    - time_unfold @T_table_push. time_simpl.
      unfold table_push. cbn [table_room table_front table_back table_front_size table_back_size].
      rewrite Nat2N.inj_succ. lia.
  Qed.

  (** Indexed table reads cost at most a constant times the requested index. *)
  Lemma table_get_clock : forall A (default : A) j t, table_valid t ->
    (T_table_get default j t <= 32 * N.of_nat (j + 1))%N.
  Proof.
    intros A default j [front back nf nb room] [Hfront [Hback Hroom]].
    cbn [table_front table_back table_front_size table_back_size table_room] in *.
    pose proof (List.T_nth_error_le front j) as Hfront_cost.
    time_unfold @T_table_get. time_simpl.
    cbn [table_front table_back table_front_size table_back_size table_room].
    destruct (nth_error front j) as [x |] eqn:Hget; time_simpl; [lia |].
    apply nth_error_None in Hget.
    assert (Hnb : nb <= j) by lia.
    pose proof (table_sub_clock j nf) as Hsub.
    set (k := table_sub j nf) in *.
    assert (Hk : k <= j) by (unfold k; rewrite table_sub_eq; lia).
    pose proof (Nat.T_leb_le (S k) nb) as Hcompare.
    destruct (Nat.leb (S k) nb); time_simpl; [| lia].
    pose proof (table_sub_clock nb (S k)) as Hreverse.
    set (r := table_sub nb (S k)) in *.
    assert (Hr : r <= nb) by (unfold r; rewrite table_sub_eq; lia).
    pose proof (List.T_nth_error_le back r) as Hback_cost.
    destruct (nth_error back r); time_simpl; lia.
  Qed.
  (** Reading all children pays for the sum of their indices. *)
  Lemma table_children_clock : forall (default : cell V.t) children t, table_valid t ->
    (ListDef.T_map (fun j => table_get default j t)
      (fun j => 1 + T_table_get default j t) children <=
      64 * N.of_nat ((fold_right (fun (j n : nat) => (j + 1 + n)%nat) 0%nat children + 1)%nat))%N.
  Proof.
    intros default children. induction children as [| j rest IH]; intros t Hvalid.
    - time_unfold ListDef.T_map. time_cbn. lia.
    - pose proof (table_get_clock _ default j t Hvalid) as Hhead.
      specialize (IH t Hvalid). time_unfold ListDef.T_map. time_simpl.
      cbn [fold_right]. rewrite !Nat2N.inj_add in *. nia.
  Qed.

  (** One fold step pays its child reads, insertion, table push and recursive call. *)
  Lemma T_build_nodes_step : forall n rest t db,
    let cells := match n with
      | EApp _ children => map (fun j => table_get (Id 1%positive) j t) children
      | ELit _ => []
      end in
    let out := add_node n cells db in
    (T_build_nodes (n :: rest) t db <=
      (match n with
       | EApp _ children => ListDef.T_map (fun j => table_get (Id 1%positive) j t)
           (fun j => 1 + T_table_get (Id 1%positive) j t) children
       | ELit _ => 0
       end) + T_add_node n cells db + T_table_push (fst out) t +
      T_build_nodes rest (table_push (fst out) t) (snd out) + 16)%N.
  Proof.
    intros [f children | v] rest t db; cbv zeta; time_unfold T_build_nodes; time_simpl.
    - destruct (add_node (EApp f children)
        (map (fun j => table_get (Id 1%positive) j t) children) db).
      time_cbn. lia.
    - time_cbn. lia.
  Qed.

  (** Expression insertion pays for its node fold, root lookup and fixed wrapper work. *)
  Lemma T_add_expr_overhead : forall e db,
    (T_add_expr e db <= T_build_nodes (expr_nodes V.t e) table_empty db +
      T_table_get (Id 1%positive) (expr_root V.t e)
        (fst (build_nodes (expr_nodes V.t e) table_empty db)) + 16)%N.
  Proof.
    intros [ns root_index] db. time_unfold T_add_expr. time_simpl.
    cbn [expr_nodes expr_root].
    destruct (build_nodes ns table_empty db) as [t final].
    destruct (table_get (Id 1%positive) root_index t); time_cbn; lia.
  Qed.
  (** Every node contributes at least one unit of insertion work. *)
  Lemma enode_work_positive : forall (n : enode V.t), 1 <= enode_work n.
  Proof.
    intros [f children | v]; cbn [enode_work]; nia.
  Qed.

  (** The optimized fold pays node costs and linear table maintenance with suffix credit. *)
  Lemma T_build_nodes_split : forall ns t db, table_valid t ->
    (T_build_nodes ns t db + 16 *
      N.of_nat (table_back_size (fst (build_nodes ns t db))) <=
      T_add_nodes ns (table_list t) db +
      256 * N.of_nat ((fold_right (fun n m => (enode_work n + m)%nat) 0%nat ns + 1)%nat) +
      16 * N.of_nat (table_back_size t))%N.
  Proof.
    induction ns as [| n rest IH]; intros t db Hvalid.
    - time_unfold T_build_nodes. cbn [T_add_nodes build_nodes fst fold_right].
      time_simpl. lia.
    - set (cells := match n with
        | EApp _ children => map (fun j => table_get (Id 1%positive) j t) children
        | ELit _ => []
        end).
      assert (Hargs : node_args n (table_list t) = cells).
      { destruct n as [f children | v]; [| reflexivity]. unfold cells, node_args.
        apply map_ext. intro j. symmetry. now apply table_get_nth. }
      pose proof (T_build_nodes_step n rest t db) as Hstep. cbv zeta in Hstep.
      fold cells in Hstep.
      assert (Hreads : ((match n with
        | EApp _ children => ListDef.T_map (fun j => table_get (Id 1%positive) j t)
            (fun j => 1 + T_table_get (Id 1%positive) j t) children
        | ELit _ => 0
        end) <= 64 * N.of_nat (enode_work n))%N).
      { destruct n as [f children | v]; [| cbn [enode_work]; lia].
        pose proof (table_children_clock (Id 1%positive) children t Hvalid) as Hchildren.
        unfold enode_work. rewrite Nat2N.inj_add. nia. }
      pose proof (enode_work_positive n) as Hpositive.
      cbn [T_add_nodes]. rewrite Hargs. cbn [build_nodes]. fold cells.
      destruct (add_node n cells db) as [c next] eqn:Hnode_result.
      cbn [fst snd] in Hstep |- *.
      pose proof (table_push_clock _ c t Hvalid) as Hpush.
      specialize (IH (table_push c t) next (table_push_valid _ c t Hvalid)).
      rewrite table_push_list in IH.
      cbn [fold_right]. rewrite !Nat2N.inj_add in IH |- *. lia.
  Qed.

  (** Changing the terminal accumulator adds exactly that amount to the node-work sum. *)
  Lemma nodes_work_offset : forall ns base,
    fold_right (fun (n : enode V.t) m => enode_work n + m) base ns =
    fold_right (fun n m => enode_work n + m) 0 ns + base.
  Proof.
    induction ns as [| n rest IH]; intro base; cbn [fold_right]; [reflexivity |].
    rewrite IH. lia.
  Qed.

  (** Expression insertion has at most a fixed linear overhead over the plan's node costs. *)
  Lemma T_add_expr_bound : forall e db,
    (T_add_expr e db <= T_add_nodes (expr_nodes V.t e) [] db +
      512 * N.of_nat (expr_work e))%N.
  Proof.
    intros [ns root_index] db.
    pose proof (T_add_expr_overhead (FExpr V.t ns root_index) db) as Hwrapper.
    pose proof (T_build_nodes_split ns table_empty db (table_empty_valid (cell V.t)))
      as Hnodes.
    pose proof (build_nodes_shape ns table_empty db (table_empty_valid (cell V.t))) as Hshape.
    cbn [expr_nodes expr_root] in Hwrapper.
    destruct (build_nodes ns table_empty db) as [t final] eqn:Hresult.
    cbn [fst snd expr_nodes expr_root] in Hwrapper, Hnodes, Hshape |- *.
    pose proof (table_get_clock _ (Id 1%positive) root_index t (proj1 Hshape)) as Hroot.
    change (T_build_nodes ns table_empty db + 16 * N.of_nat (table_back_size t) <=
      T_add_nodes ns [] db +
      256 * N.of_nat ((fold_right (fun n m => (enode_work n + m)%nat) 0%nat ns + 1)%nat) +
      16 * 0)%N
      in Hnodes.
    unfold expr_work. cbn [expr_nodes expr_root]. rewrite nodes_work_offset.
    rewrite !Nat2N.inj_add in Hnodes, Hroot |- *. lia.
  Qed.
  (** One node preserves the prepared prefix, layout and monotone budgets needed by cost folds. *)
  Lemma node_prefix_ready : forall ds n rest t db, D.wf db ->
    (forall f, kind (D.view db) f = lookup_kind ds f) ->
    table_valid t -> table_allocated db t ->
    nodes_typed ds (map cell_sort (table_list t)) (n :: rest) ->
    Forall (fun node => match node with
      | EApp f children => D.slots_fit db f (S (length children))
      | ELit _ => True
      end) (n :: rest) ->
    let cells := match n with
      | EApp _ children => map (fun j => table_get (Id 1%positive) j t) children
      | ELit _ => []
      end in
    let out := add_node n cells db in
    let t' := table_push (fst out) t in
    D.wf (snd out) /\ kind (D.view (snd out)) = kind (D.view db) /\
    D.slots (snd out) = D.slots db /\ (D.ids db <= D.ids (snd out))%N /\
    D.unit db <= D.unit (snd out) /\ table_valid t' /\ table_allocated (snd out) t' /\
    nodes_typed ds (map cell_sort (table_list t')) rest /\
    Forall (fun node => match node with
      | EApp f children => D.slots_fit (snd out) f (S (length children))
      | ELit _ => True
      end) rest.
  Proof.
    intros ds n rest t db Hwf Hkind Hvalid Hallocated [Hnode Htail] Hslots.
    apply Forall_cons_iff in Hslots. destruct Hslots as [Hslot Hslots].
    set (cells := match n with
      | EApp _ children => map (fun j => table_get (Id 1%positive) j t) children
      | ELit _ => []
      end).
    assert (Hready : (forall i, In (Id i) cells -> D.allocated db i) /\
      match n with
      | EApp f _ => kind (D.view db) f = Some OId /\
          D.slots_fit db f (S (length cells))
      | ELit _ => True
      end).
    { destruct n as [f children | v]; unfold cells; cbn in *.
      - destruct Hnode as [Hf [ss [Hss Hchildren]]].
        destruct (table_children_typed db t children ss Hvalid Hallocated Hchildren)
          as [Hsorts Hids].
        split; [exact Hids |]. split; [now rewrite Hkind | now rewrite length_map].
      - split; [intros i Hin; contradiction | exact I]. }
    destruct Hready as [Hcells Hready].
    pose proof (add_node_ready n cells db Hwf Hcells Hready) as Hnext.
    pose proof (add_node_sort n cells db) as Hsort.
    pose proof (add_node_unit n cells db Hwf) as Hunit.
    cbv zeta. fold cells.
    destruct (add_node n cells db) as [c next] eqn:Hnode_result.
    cbn [fst snd] in Hnext, Hsort, Hunit |- *.
    destruct Hnext as [Hwf' [Hkind' [Hslots' [Hnew [Hids Hgrowth]]]]].
    split; [exact Hwf' |]. split; [exact Hkind' |]. split; [exact Hslots' |].
    split; [exact Hids |]. split; [exact Hunit |]. split.
    - now apply table_push_valid.
    - split.
      + unfold table_allocated in *. rewrite table_push_list. apply Forall_app. split.
        * eapply Forall_impl; [| exact Hallocated]. intros old Hold i Heq.
          specialize (Hold i Heq). unfold D.allocated in *.
          exact (N.le_trans _ _ _ Hold Hids).
        * constructor; [exact Hnew | constructor].
      + split.
        * rewrite table_push_list, map_app. cbn [map]. now rewrite Hsort.
        * eapply Forall_impl; [| exact Hslots]. intros [f children | v] Hfits; [| exact I].
          unfold D.slots_fit in *. now rewrite Hslots'.
  Qed.

  (** The node fold retains its slot layout and never reduces either spending budget. *)
  Lemma build_nodes_economy : forall ds ns t db, D.wf db ->
    (forall f, kind (D.view db) f = lookup_kind ds f) ->
    table_valid t -> table_allocated db t ->
    nodes_typed ds (map cell_sort (table_list t)) ns ->
    Forall (fun node => match node with
      | EApp f children => D.slots_fit db f (S (length children))
      | ELit _ => True
      end) ns ->
    D.wf (snd (build_nodes ns t db)) /\
    D.slots (snd (build_nodes ns t db)) = D.slots db /\
    (D.ids db <= D.ids (snd (build_nodes ns t db)))%N /\
    D.unit db <= D.unit (snd (build_nodes ns t db)).
  Proof.
    intros ds ns. induction ns as [| n rest IH]; intros t db Hwf Hkind Hvalid Hallocated
      Htyped Hslots.
    - cbn [build_nodes snd]. split; [exact Hwf |]. split; [reflexivity |].
      split; [apply N.le_refl | apply Nat.le_refl].
    - pose proof (node_prefix_ready ds n rest t db Hwf Hkind Hvalid Hallocated Htyped Hslots)
        as Hstep.
      set (cells := match n with
        | EApp _ children => map (fun j => table_get (Id 1%positive) j t) children
        | ELit _ => []
        end).
      cbv zeta in Hstep. fold cells in Hstep. cbn [build_nodes]. fold cells.
      destruct (add_node n cells db) as [c next] eqn:Hnode_result.
      cbn [fst snd] in Hstep |- *.
      destruct Hstep as [Hwf' [Hkind' [Hslots' [Hids [Hunit [Hvalid'
        [Hallocated' [Htyped' Hfits']]]]]]]].
      assert (Hkind_next : forall f, kind (D.view next) f = lookup_kind ds f).
      { intro f. now rewrite Hkind'. }
      destruct (IH (table_push c t) next Hwf' Hkind_next Hvalid' Hallocated' Htyped' Hfits')
        as [Hfinal [Hlayout [Hids_final Hunit_final]]].
      split; [exact Hfinal |]. split; [now rewrite Hlayout, Hslots' |]. split.
      + exact (N.le_trans _ _ _ Hids Hids_final).
      + exact (Nat.le_trans _ _ _ Hunit Hunit_final).
  Qed.
  (** A prepared node spends at most its own work in the common final budget. *)
  Lemma prepared_node_amort : forall B U ds n rest t db, D.wf db ->
    (forall f, kind (D.view db) f = lookup_kind ds f) ->
    table_valid t -> table_allocated db t ->
    nodes_typed ds (map cell_sort (table_list t)) (n :: rest) ->
    Forall (fun node => match node with
      | EApp f children => D.slots_fit db f (S (length children))
      | ELit _ => True
      end) (n :: rest) ->
    let cells := match n with
      | EApp _ children => map (fun j => table_get (Id 1%positive) j t) children
      | ELit _ => []
      end in
    (D.ids (snd (add_node n cells db)) <= B)%N ->
    D.unit (snd (add_node n cells db)) <= U ->
    (T_add_node n cells db + N.of_nat U * D.potential B (snd (add_node n cells db)) <=
      128 * (D.c_db + 1) * N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) *
        N.of_nat (D.num_slots db + 1) * N.of_nat (enode_work n) +
      N.of_nat U * D.potential B db)%N.
  Proof.
    intros B U ds n rest t db Hwf Hkind Hvalid Hallocated [Hnode Htail] Hslots.
    apply Forall_cons_iff in Hslots. destruct Hslots as [Hslot Hslots].
    set (cells := match n with
      | EApp _ children => map (fun j => table_get (Id 1%positive) j t) children
      | ELit _ => []
      end). cbv zeta. fold cells. intros Hids HU.
    assert (Hready : (forall i, In (Id i) cells -> D.allocated db i) /\
      match n with
      | EApp f _ => kind (D.view db) f = Some OId /\
          D.slots_fit db f (S (length cells))
      | ELit _ => cells = []
      end).
    { destruct n as [f children | v]; unfold cells; cbn in *.
      - destruct Hnode as [Hf [ss [Hss Hchildren]]].
        destruct (table_children_typed db t children ss Hvalid Hallocated Hchildren)
          as [Hsorts Hids'].
        split; [exact Hids' |]. split; [now rewrite Hkind | now rewrite length_map].
      - split; [intros i Hin; contradiction | reflexivity]. }
    destruct Hready as [Hcells Hready].
    pose proof (add_node_amort_bound B U n cells db Hwf Hcells Hready Hids HU) as Hcost.
    assert (Hwidth : (N.of_nat ((length cells + 2) * (length cells + 2)) <=
      4 * N.of_nat (enode_work n))%N).
    { destruct n as [f children | v]; unfold cells, enode_work.
      - rewrite length_map, Nat2N.inj_add. nia.
      - reflexivity. }
    eapply N.le_trans; [exact Hcost |]. apply N.add_le_mono_r.
    replace (128 * (D.c_db + 1) * N.of_nat U *
      N.of_nat (N.to_nat (N.log2 B) + 1) * N.of_nat (D.num_slots db + 1) *
      N.of_nat (enode_work n))%N with
      ((32 * (D.c_db + 1) * N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) *
        N.of_nat (D.num_slots db + 1)) * (4 * N.of_nat (enode_work n)))%N by ring.
    now apply N.mul_le_mono_l.
  Qed.

  (** The node fold telescopes insertion potential at its final identifier and unit budgets. *)
  Lemma T_add_nodes_amort : forall B U ds ns t db, D.wf db ->
    (forall f, kind (D.view db) f = lookup_kind ds f) ->
    table_valid t -> table_allocated db t ->
    nodes_typed ds (map cell_sort (table_list t)) ns ->
    Forall (fun node => match node with
      | EApp f children => D.slots_fit db f (S (length children))
      | ELit _ => True
      end) ns ->
    (D.ids (snd (build_nodes ns t db)) <= B)%N ->
    D.unit (snd (build_nodes ns t db)) <= U ->
    (T_add_nodes ns (table_list t) db +
      N.of_nat U * D.potential B (snd (build_nodes ns t db)) <=
      128 * (D.c_db + 1) * N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) *
        N.of_nat (D.num_slots db + 1) *
        N.of_nat (fold_right (fun n m => (enode_work n + m)%nat) 0%nat ns) +
      N.of_nat U * D.potential B db)%N.
  Proof.
    intros B U ds ns. induction ns as [| n rest IH]; intros t db Hwf Hkind Hvalid Hallocated
      Htyped Hslots Hids HU.
    - cbn [T_add_nodes build_nodes snd fold_right]. nia.
    - pose proof (node_prefix_ready ds n rest t db Hwf Hkind Hvalid Hallocated Htyped Hslots)
        as Hstep.
      pose proof (prepared_node_amort B U ds n rest t db Hwf Hkind Hvalid Hallocated
        Htyped Hslots) as Hcost.
      set (cells := match n with
        | EApp _ children => map (fun j => table_get (Id 1%positive) j t) children
        | ELit _ => []
        end).
      assert (Hargs : node_args n (table_list t) = cells).
      { destruct n as [f children | v]; [| reflexivity]. unfold cells, node_args.
        apply map_ext. intro j. symmetry. now apply table_get_nth. }
      cbv zeta in Hstep, Hcost. fold cells in Hstep, Hcost.
      cbn [T_add_nodes]. rewrite Hargs.
      cbn [build_nodes] in Hids, HU |- *. fold cells in Hids, HU |- *.
      destruct (add_node n cells db) as [c next] eqn:Hnode_result.
      cbn [fst snd] in Hstep, Hcost, Hids, HU |- *.
      destruct Hstep as [Hwf' [Hkind' [Hslots' [Hids' [Hunit' [Hvalid'
        [Hallocated' [Htyped' Hfits']]]]]]]].
      assert (Hkind_next : forall f, kind (D.view next) f = lookup_kind ds f).
      { intro f. now rewrite Hkind'. }
      destruct (build_nodes_economy ds rest (table_push c t) next Hwf' Hkind_next
        Hvalid' Hallocated' Htyped' Hfits') as [Hfinal [Hlayout [Hids_final Hunit_final]]].
      specialize (Hcost (N.le_trans _ _ _ Hids_final Hids)
        (Nat.le_trans _ _ _ Hunit_final HU)).
      specialize (IH (table_push c t) next Hwf' Hkind_next Hvalid' Hallocated' Htyped' Hfits'
        Hids HU).
      rewrite table_push_list in IH.
      assert (Hnum_slots : D.num_slots next = D.num_slots db).
      { unfold D.num_slots. now rewrite Hslots'. }
      rewrite Hnum_slots in IH. cbn [fold_right]. rewrite Nat2N.inj_add.
      rewrite N.mul_add_distr_l. lia.
  Qed.
  (** Adding an expression separates node insertion cost from child-index work. *)
  Lemma T3_add_expr_split : forall e db,
    (T_add_expr e db <= T_add_nodes (expr_nodes V.t e) [] db +
      k_sat * N.of_nat (expr_work e))%N.
  Proof.
    intros e db. eapply N.le_trans; [apply T_add_expr_bound |].
    apply N.add_le_mono_l. apply N.mul_le_mono_r. unfold k_sat. nia.
  Qed.
  (** Adding a node pays its insertion cost and transfers the database potential. *)
  Lemma T4_add_node_amort : forall B U node cells db, D.wf db ->
    (forall i, In (Id i) cells -> D.allocated db i) ->
    match node with
    | EApp f _ => kind (D.view db) f = Some OId /\ D.slots_fit db f (S (length cells))
    | ELit _ => cells = []
    end ->
    (D.ids (snd (add_node node cells db)) <= B)%N ->
    D.unit (snd (add_node node cells db)) <= U ->
    (T_add_node node cells db + N.of_nat U * D.potential B (snd (add_node node cells db)) <=
      k_sat * N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) *
        N.of_nat (D.num_slots db + 1) * N.of_nat ((length cells + 2) * (length cells + 2)) +
      N.of_nat U * D.potential B db)%N.
  Proof.
    intros B U node cells db Hwf Hallocated Hnode Hids HU.
    pose proof (add_node_amort_bound B U node cells db Hwf Hallocated Hnode Hids HU)
      as Hcost.
    eapply N.le_trans; [exact Hcost |]. apply N.add_le_mono_r.
    do 4 apply N.mul_le_mono_r. unfold k_sat. nia.
  Qed.
  (** Expression insertion returns exactly the database produced by its node fold. *)
  Lemma add_expr_db : forall e db,
    snd (add_expr e db) = snd (build_nodes (expr_nodes V.t e) table_empty db).
  Proof.
    intros [ns root_index] db. unfold add_expr. cbn [expr_nodes].
    destruct (build_nodes ns table_empty db) as [t final].
    destruct (table_get (Id 1%positive) root_index t); reflexivity.
  Qed.

  (** Input insertion combines node potential transfer with the optimized table overhead. *)
  Lemma add_expr_amort_bound : forall B U ds e db, D.wf db -> expr_ok ds db e ->
    (D.ids (snd (add_expr e db)) <= B)%N -> D.unit (snd (add_expr e db)) <= U ->
    (T_add_expr e db + N.of_nat U * D.potential B (snd (add_expr e db)) <=
      1024 * (D.c_db + 1) * N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) *
        N.of_nat (D.num_slots db + 1) * N.of_nat (expr_work e) +
      N.of_nat U * D.potential B db)%N.
  Proof.
    intros B U ds [ns root_index] db Hwf [Hexpr [Hkind Hslots]] Hids HU.
    rewrite add_expr_db in Hids, HU |- *. cbn [expr_nodes] in Hids, HU |- *.
    pose proof (expr_nodes_typed V.t ds (FExpr V.t ns root_index) Hexpr) as Htyped.
    assert (Hallocated : table_allocated db (@table_empty (cell V.t))) by constructor.
    pose proof (T_add_nodes_amort B U ds ns table_empty db Hwf Hkind
      (table_empty_valid (cell V.t)) Hallocated Htyped Hslots Hids HU) as Hnodes.
    pose proof (T_add_expr_bound (FExpr V.t ns root_index) db) as Hclock.
    destruct (build_nodes_economy ds ns table_empty db Hwf Hkind
      (table_empty_valid (cell V.t)) Hallocated Htyped Hslots)
      as [Hwf' [Hlayout [Hids_mono Hunit_mono]]].
    assert (Hunit : D.unit db <= U) by lia.
    pose proof (node_budget_positive B U db 1 Hunit (Nat.le_refl 1)) as Hpositive.
    set (q := (N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) *
      N.of_nat (D.num_slots db + 1))%N).
    change (1 <= q * 1)%N in Hpositive. rewrite N.mul_1_r in Hpositive.
    assert (Hsum : (N.of_nat (fold_right (fun n m => (enode_work n + m)%nat) 0%nat ns) <=
      N.of_nat (expr_work (FExpr V.t ns root_index)))%N).
    { unfold expr_work. cbn [expr_nodes expr_root].
      rewrite (nodes_work_offset ns (root_index + 1)). lia. }
    change (T_add_nodes ns [] db + N.of_nat U *
      D.potential B (snd (build_nodes ns table_empty db)) <=
      128 * (D.c_db + 1) * N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) *
        N.of_nat (D.num_slots db + 1) *
        N.of_nat (fold_right (fun n m => (enode_work n + m)%nat) 0%nat ns) +
      N.of_nat U * D.potential B db)%N in Hnodes.
    replace (128 * (D.c_db + 1) * N.of_nat U *
      N.of_nat (N.to_nat (N.log2 B) + 1) * N.of_nat (D.num_slots db + 1))%N
      with (128 * ((D.c_db + 1) * q))%N in Hnodes by (unfold q; ring).
    replace (1024 * (D.c_db + 1) * N.of_nat U *
      N.of_nat (N.to_nat (N.log2 B) + 1) * N.of_nat (D.num_slots db + 1))%N
      with (1024 * ((D.c_db + 1) * q))%N by (unfold q; ring).
    set (r := ((D.c_db + 1) * q)%N) in *.
    assert (Hr : (1 <= r)%N) by (unfold r; nia).
    assert (Hsum_paid : (r *
      N.of_nat (fold_right (fun n m => (enode_work n + m)%nat) 0%nat ns) <=
      r * N.of_nat (expr_work (FExpr V.t ns root_index)))%N).
    { now apply N.mul_le_mono_l. }
    assert (Hwork_paid : (N.of_nat (expr_work (FExpr V.t ns root_index)) <=
      r * N.of_nat (expr_work (FExpr V.t ns root_index)))%N) by nia.
    cbn [expr_nodes] in Hclock. nia.
  Qed.

  (** Adding accepted inputs never lowers the database's spending unit. *)
  Lemma inputs_unit_mono : forall ds es db, D.wf db ->
    view_sorted (lookup_sorts ds) (D.view db) -> Forall (expr_ok ds db) es ->
    D.unit db <= D.unit (inputs_db es db).
  Proof.
    intros ds es. induction es as [| e rest IH]; intros db Hwf Hsorted Hexprs;
      cbn [inputs_db]; [apply Nat.le_refl |].
    apply Forall_cons_iff in Hexprs. destruct Hexprs as [Hexpr Hrest].
    destruct (F2_add_expr_wf ds e db Hwf Hexpr Hsorted)
      as [Hwf' [Hsorted' [Hkind [Hslots [Hallocated [Hids Hunit]]]]]].
    assert (Hrest' : Forall (expr_ok ds (snd (add_expr e db))) rest).
    { eapply Forall_impl; [| exact Hrest]. intros x Hx.
      exact (expr_ok_layout ds db (snd (add_expr e db)) x Hkind Hslots Hx). }
    eapply Nat.le_trans; [exact Hunit |]. now apply IH.
  Qed.

  (** The ordered input cost telescopes potential at one common final spending budget. *)
  Lemma T_inputs_amort : forall B U ds es db, D.wf db ->
    view_sorted (lookup_sorts ds) (D.view db) -> Forall (expr_ok ds db) es ->
    (D.ids (inputs_db es db) <= B)%N -> D.unit (inputs_db es db) <= U ->
    (T_inputs es db + N.of_nat U * D.potential B (inputs_db es db) <=
      1024 * (D.c_db + 1) * N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) *
        N.of_nat (D.num_slots db + 1) *
        N.of_nat (fold_right (fun e n => (expr_work e + 1 + n)%nat) 1%nat es) +
      N.of_nat U * D.potential B db)%N.
  Proof.
    intros B U ds es. induction es as [| e rest IH]; intros db Hwf Hsorted Hexprs Hids HU;
      cbn [T_inputs inputs_db fold_right] in Hids, HU |- *.
    - pose proof (node_budget_positive B U db 1 HU (Nat.le_refl 1)) as Hpositive.
      change (1 <= N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) *
        N.of_nat (D.num_slots db + 1) * 1)%N in Hpositive.
      rewrite N.mul_1_r in Hpositive |- *.
      set (q := (N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) *
        N.of_nat (D.num_slots db + 1))%N) in *.
      replace (1024 * (D.c_db + 1) * N.of_nat U *
        N.of_nat (N.to_nat (N.log2 B) + 1) * N.of_nat (D.num_slots db + 1))%N
        with (1024 * (D.c_db + 1) * q)%N by (unfold q; ring). nia.
    - apply Forall_cons_iff in Hexprs. destruct Hexprs as [Hexpr Hrest].
      destruct (F2_add_expr_wf ds e db Hwf Hexpr Hsorted)
        as [Hwf' [Hsorted' [Hkind [Hslots [Hallocated [Hids' Hunit']]]]]].
      set (next := snd (add_expr e db)) in *.
      assert (Hrest' : Forall (expr_ok ds next) rest).
      { eapply Forall_impl; [| exact Hrest]. intros x Hx.
        exact (expr_ok_layout ds db next x Hkind Hslots Hx). }
      destruct (add_inputs_properties ds rest next Hwf' Hsorted' Hrest')
        as [Hfinal [Hsorted_final [Hkind_final [Hslots_final [Hids_final Hgrowth]]]]].
      rewrite add_inputs_db in Hids_final.
      pose proof (inputs_unit_mono ds rest next Hwf' Hsorted' Hrest') as Hunit_final.
      pose proof (add_expr_amort_bound B U ds e db Hwf Hexpr
        (N.le_trans _ _ _ Hids_final Hids) (Nat.le_trans _ _ _ Hunit_final HU)) as Hhead.
      fold next in Hhead.
      specialize (IH next Hwf' Hsorted' Hrest' Hids HU).
      assert (Hnum_slots : D.num_slots next = D.num_slots db).
      { unfold D.num_slots. now rewrite Hslots. }
      rewrite Hnum_slots in IH.
      assert (Hunit : D.unit db <= U) by lia.
      pose proof (node_budget_positive B U db 1 Hunit (Nat.le_refl 1)) as Hpositive.
      change (1 <= N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) *
        N.of_nat (D.num_slots db + 1) * 1)%N in Hpositive.
      rewrite N.mul_1_r in Hpositive.
      set (q := (N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) *
        N.of_nat (D.num_slots db + 1))%N) in Hpositive.
      set (r := (1024 * (D.c_db + 1) * N.of_nat U *
        N.of_nat (N.to_nat (N.log2 B) + 1) * N.of_nat (D.num_slots db + 1))%N) in *.
      assert (Hr : (1 <= r)%N).
      { unfold r. replace (1024 * (D.c_db + 1) * N.of_nat U *
          N.of_nat (N.to_nat (N.log2 B) + 1) * N.of_nat (D.num_slots db + 1))%N
          with (1024 * (D.c_db + 1) * q)%N by (unfold q; ring). nia. }
      rewrite !Nat2N.inj_add, !N.mul_add_distr_l, N.mul_1_r. lia.
  Qed.

  (** Adding an expression transfers scaled potential at the result's spending budgets. *)
  Lemma T_add_expr_amort : forall B U ds e db, D.wf db -> expr_ok ds db e ->
    (D.ids (snd (add_expr e db)) <= B)%N -> D.unit (snd (add_expr e db)) <= U ->
    (T_add_expr e db + N.of_nat U * D.potential B (snd (add_expr e db)) <=
      c_sat * N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) *
        N.of_nat (D.num_slots db + 1) * N.of_nat (expr_work e) +
      N.of_nat U * D.potential B db)%N.
  Proof.
    intros B U ds e db Hwf Hexpr Hids HU.
    eapply N.le_trans; [exact (add_expr_amort_bound B U ds e db Hwf Hexpr Hids HU) |].
    apply N.add_le_mono_r. do 4 apply N.mul_le_mono_r. unfold c_sat. nia.
  Qed.

  (** Adding inputs pays for their nodes at the final unit and identifier budget. *)
  Lemma T_inputs_le : forall B U ds rws ans es, front_ok ds rws ans es ->
    let p := C.compile ds rws ans in
    let db0 := E.load p (E.plan p) in
    (D.ids (inputs_db es db0) <= B)%N -> D.unit (inputs_db es db0) <= U ->
    (T_inputs es db0 + N.of_nat U * D.potential B (inputs_db es db0) <=
      c_sat * N.of_nat U * N.of_nat (N.to_nat (N.log2 B) + 1) *
        N.of_nat (D.num_slots db0 + 1) *
        N.of_nat (fold_right (fun e n => (expr_work e + 1 + n)%nat) 1%nat es))%N.
  Proof.
    intros B U ds rws ans es [Hrules Hexprs]. cbv zeta. intros Hids HU.
    set (p := C.compile ds rws ans) in *.
    set (cp := E.plan p) in *.
    assert (Hdecls : decls V.t p = ds) by apply C.compile_program.
    assert (Hplan : E.plans_ok p cp).
    { apply E.plan_checked. now apply C.compile_sorted. }
    destruct (load_properties p cp) as [Hwf Hloaded].
    assert (Hsorted : view_sorted (lookup_sorts ds) (D.view (E.load p cp))).
    { destruct Hloaded as [Hkind [Hslots Hsort]].
      unfold program_sorts in Hsort. now rewrite Hdecls in Hsort. }
    assert (Hinputs : Forall (expr_ok ds (E.load p cp)) es).
    { eapply Forall_impl; [| exact Hexprs]. intros e Hexpr.
      exact (loaded_expr_ok p cp ds (E.load p cp) e Hdecls Hplan Hloaded Hexpr). }
    pose proof (T_inputs_amort B U ds es (E.load p cp) Hwf Hsorted Hinputs Hids HU) as Hcost.
    assert (Hzero : D.potential B (E.load p cp) = 0%N).
    { rewrite E.load_spec. apply D.potential_init. }
    rewrite Hzero, N.mul_0_r, N.add_0_r in Hcost.
    eapply N.le_trans; [exact Hcost |].
    do 4 apply N.mul_le_mono_r. unfold c_sat. nia.
  Qed.
End SaturateT.
