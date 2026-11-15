(** * Indexed liveness producer

    Reverse graph searches collect live variables at the entry point of each block.
    For example, a use propagates to predecessors until an edge defines its variable.
    Builds on: LiveSig and positive tries. *)

From Stdlib Require Import List PArith NArith Bool Lia.
From Argent Require Import Time Tactics Std BigO.
From Galois.Base Require Import KeySig Key Trie.
From Galois.Graph Require Import DigraphSig.
From Galois.Program Require Import CfgSig VarsSig SsaSig.
From Galois.Ssa Require Import Lang LiveSig.
Import List.ListNotations.

(** Lookup stops at an absent subtree, even when the requested key is unusually wide. *)
Fixpoint live_lookup {A} (key : positive) (table : ptrie A) : option A :=
  match table with
  | Empty => None
  | Nodes _ =>
    match key with
    | xH => trie_value table
    | xO rest => live_lookup rest (trie_left table)
    | xI rest => live_lookup rest (trie_right table)
    end
  end.
TimeFun live_lookup.

Definition live_member (key : positive) (table : ptrie unit) : bool :=
  match trie_get key table with Some _ => true | None => false end.
TimeFun live_member.

(** A row records its own membership index and its distinct points. *)
Definition live_seed {A} (encode : A -> positive) (n : A) (x : positive)
    (table : ptrie (ptrie unit * list A)) : ptrie (ptrie unit * list A) :=
  let row := match trie_get x table with Some old => old | None => (Empty, []) end in
  if live_member (encode n) (fst row) then table else
    PTrieCode.set x (PTrieCode.set (encode n) tt (fst row), n :: snd row) table.
TimeFun live_seed.

Definition live_seed_batch {A B} (encode : A -> positive) (point : B -> A)
    (values : B -> list positive) (items : list B)
    (table : ptrie (ptrie unit * list A)) : ptrie (ptrie unit * list A) :=
  fold_right (fun item acc =>
    fold_right (live_seed encode (point item)) acc (values item)) table items.
TimeFun live_seed_batch.

(** On another parallel edge, only definitions present on both edges remain kills. *)
Fixpoint live_intersection (defs : list positive) (old : option (ptrie unit))
    : ptrie unit :=
  match defs with
  | [] => Empty
  | x :: rest =>
    let tail := live_intersection rest old in
    match old with
    | None => PTrieCode.set x tt tail
    | Some row => if live_member x row then PTrieCode.set x tt tail else tail
    end
  end.
TimeFun live_intersection.

Definition live_kill_add (src dst : positive) (defs : list positive)
    (table : ptrie (ptrie (ptrie unit))) : ptrie (ptrie (ptrie unit)) :=
  let row := match trie_get dst table with Some row => row | None => Empty end in
  PTrieCode.set dst (PTrieCode.set src (live_intersection defs (trie_get src row)) row)
    table.
TimeFun live_kill_add.

Definition live_kill_row (table : ptrie (ptrie (ptrie unit))) (src dst : positive)
    : option (ptrie unit) :=
  match trie_get dst table with
  | None => None
  | Some row => trie_get src row
  end.
TimeFun live_kill_row.

Definition live_killed (table : ptrie (ptrie (ptrie unit))) (src dst x : positive)
    : bool :=
  match live_kill_row table src dst with
  | None => false
  | Some defs => live_member x defs
  end.
TimeFun live_killed.

Record live_state (A : Type) := {
  live_seen : ptrie unit;
  live_todo : list A;
  live_done : list A
}.
Arguments live_seen {A}.
Arguments live_todo {A}.
Arguments live_done {A}.
TimeFun live_seen.
TimeFun live_todo.
TimeFun live_done.

Definition live_discover {A} (encode : A -> positive) (n : A) (st : live_state A)
    : live_state A :=
  if live_member (encode n) (live_seen st) then st else
    {| live_seen := PTrieCode.set (encode n) tt (live_seen st);
       live_todo := n :: live_todo st;
       live_done := n :: live_done st |}.
TimeFun live_discover.

Definition live_initial {A} (encode : A -> positive) (seeds : list A) : live_state A :=
  fold_right (live_discover encode)
    {| live_seen := Empty; live_todo := []; live_done := [] |} seeds.
TimeFun live_initial.

Lemma live_lookup_correct : forall A key (table : ptrie A),
  live_lookup key table = trie_get key table.
Proof.
  intros A key; induction key as [key IH|key IH|]; intro table; destruct table.
  - change (None = trie_get (xI key) (@Empty A)). symmetry; apply PTrie.get_empty.
  - cbn [live_lookup trie_get]. apply IH.
  - change (None = trie_get (xO key) (@Empty A)). symmetry; apply PTrie.get_empty.
  - cbn [live_lookup trie_get]. apply IH.
  - reflexivity.
  - reflexivity.
Qed.

Lemma live_member_spec : forall key table,
  live_member key table = true <-> trie_get key table = Some tt.
Proof.
  intros key table; unfold live_member; destruct (trie_get key table) as [[]|];
    split; congruence.
Qed.

Lemma live_member_set : forall old key query,
  live_member query (PTrieCode.set key tt old) = true <->
    query = key \/ live_member query old = true.
Proof.
  intros old key query. rewrite !live_member_spec.
  destruct (Pos.eq_dec query key) as [Heq|Hneq].
  - subst query. rewrite PTrie.get_set_same. tauto.
  - rewrite PTrie.get_set_other by exact Hneq. tauto.
Qed.

Definition live_valid {A} (encode : A -> positive) (st : live_state A) : Prop :=
  NoDup (live_done st) /\
  (forall n, live_member (encode n) (live_seen st) = true <-> In n (live_done st)) /\
  NoDup (live_todo st) /\ incl (live_todo st) (live_done st).

Lemma live_discover_valid : forall A (encode : A -> positive),
  (forall a b, encode a = encode b -> a = b) -> forall st n,
  live_valid encode st -> live_valid encode (live_discover encode n st).
Proof.
  intros A encode Hinj st n [Hdone [Hseen [Htodo Hsub]]].
  unfold live_discover. destruct (live_member (encode n) (live_seen st)) eqn:Hn.
  - exact (conj Hdone (conj Hseen (conj Htodo Hsub))).
  - assert (Hfresh : ~ In n (live_done st)).
    { intro Hin. apply Hseen in Hin. congruence. }
    split; cbn.
    + constructor; assumption.
    + split.
      * intro m. rewrite live_member_set, Hseen. split.
        -- intros [Heq|Hin]; [left; symmetry; now apply Hinj|now right].
        -- intros [Heq|Hin]; [left; now subst|now right].
      * split; [constructor; [intro Hin; apply Hfresh, Hsub, Hin|exact Htodo]|].
        intros m [Heq|Hin]; [now left|right; now apply Hsub].
Qed.

Lemma live_discover_done : forall A (encode : A -> positive) st n,
  live_valid encode st -> forall m,
  In m (live_done (live_discover encode n st)) <-> m = n \/ In m (live_done st).
Proof.
  intros A encode st n [_ [Hseen _]] m. unfold live_discover.
  destruct (live_member (encode n) (live_seen st)) eqn:Hn; cbn.
  - apply Hseen in Hn. split; [now right|intros [->|Hin]; assumption].
  - split; intros [Heq|Hin]; [left; symmetry|now right|left; symmetry|now right]; assumption.
Qed.

Lemma live_discover_todo : forall A (encode : A -> positive) st n,
  live_valid encode st -> forall m,
  In m (live_todo (live_discover encode n st)) <->
    (m = n /\ ~ In n (live_done st)) \/ In m (live_todo st).
Proof.
  intros A encode st n [_ [Hseen _]] m. unfold live_discover.
  destruct (live_member (encode n) (live_seen st)) eqn:Hn; cbn.
  - apply Hseen in Hn. tauto.
  - assert (Hfresh : ~ In n (live_done st)).
    { intro Hin. apply Hseen in Hin. congruence. }
    split; intros [Heq|Hin].
    + left; split; [now symmetry|exact Hfresh].
    + now right.
    + left; symmetry; tauto.
    + now right.
Qed.

Lemma live_discover_balance : forall A (encode : A -> positive) st n,
  length (live_done (live_discover encode n st)) + length (live_todo st) =
    length (live_done st) + length (live_todo (live_discover encode n st)).
Proof.
  intros A encode st n. unfold live_discover.
  destruct (live_member (encode n) (live_seen st)); cbn; lia.
Qed.

Lemma live_initial_valid : forall A (encode : A -> positive),
  (forall a b, encode a = encode b -> a = b) -> forall seeds,
  live_valid encode (live_initial encode seeds).
Proof.
  intros A encode Hinj seeds; induction seeds as [|n rest IH].
  - unfold live_initial, live_valid; cbn. split; [constructor|]. split.
    + intro n. unfold live_member. rewrite PTrie.get_empty.
      split; [discriminate|contradiction].
    + split; [constructor|intros n Hin; contradiction].
  - cbn [live_initial fold_right]. apply live_discover_valid; assumption.
Qed.

Lemma live_initial_done : forall A (encode : A -> positive),
  (forall a b, encode a = encode b -> a = b) -> forall seeds n,
  In n (live_done (live_initial encode seeds)) <-> In n seeds.
Proof.
  intros A encode Hinj seeds; induction seeds as [|m rest IH]; intro n.
  - reflexivity.
  - cbn [live_initial fold_right]. rewrite live_discover_done.
    + rewrite IH. cbn. split; intros [Heq|Hin];
        [left; symmetry|now right|left; symmetry|now right]; assumption.
    + apply live_initial_valid, Hinj.
Qed.

Lemma live_initial_todo : forall A (encode : A -> positive) seeds,
  live_todo (live_initial encode seeds) = live_done (live_initial encode seeds).
Proof.
  intros A encode seeds; induction seeds as [|n rest IH]; [reflexivity|].
  change (live_todo (live_discover encode n (live_initial encode rest)) =
    live_done (live_discover encode n (live_initial encode rest))).
  remember (live_initial encode rest) as st in *.
  unfold live_discover. destruct (live_member (encode n) (live_seen st)); cbn;
    now rewrite IH.
Qed.

Definition live_seed_row {A} (table : ptrie (ptrie unit * list A)) (x : positive)
    : ptrie unit * list A :=
  match trie_get x table with Some row => row | None => (Empty, []) end.

Lemma live_seed_row_set_same : forall A table x (row : ptrie unit * list A),
  live_seed_row (PTrieCode.set x row table) x = row.
Proof.
  intros A table x row. unfold live_seed_row. now rewrite PTrie.get_set_same.
Qed.

Lemma live_seed_row_set_other : forall A table x y (row : ptrie unit * list A),
  y <> x -> live_seed_row (PTrieCode.set x row table) y = live_seed_row table y.
Proof.
  intros A table x y row Hneq. unfold live_seed_row.
  now rewrite PTrie.get_set_other by exact Hneq.
Qed.

Definition live_seed_valid {A} (encode : A -> positive)
    (table : ptrie (ptrie unit * list A)) : Prop :=
  forall x, NoDup (snd (live_seed_row table x)) /\ forall n,
    live_member (encode n) (fst (live_seed_row table x)) = true <->
      In n (snd (live_seed_row table x)).

Lemma live_seed_empty : forall A (encode : A -> positive),
  live_seed_valid encode Empty.
Proof.
  intros A encode x. unfold live_seed_row; rewrite PTrie.get_empty; cbn.
  split; [constructor|]. intro n. unfold live_member; rewrite PTrie.get_empty.
  split; [discriminate|contradiction].
Qed.

Lemma live_seed_valid_add : forall A (encode : A -> positive),
  (forall a b, encode a = encode b -> a = b) -> forall table n x,
  live_seed_valid encode table -> live_seed_valid encode (live_seed encode n x table).
Proof.
  intros A encode Hinj table n x Hvalid. unfold live_seed.
  change (live_seed_valid encode
    (if live_member (encode n) (fst (live_seed_row table x)) then table else
      PTrieCode.set x
        (PTrieCode.set (encode n) tt (fst (live_seed_row table x)),
          n :: snd (live_seed_row table x)) table)).
  destruct (live_member (encode n) (fst (live_seed_row table x))) eqn:Hn;
    [exact Hvalid|].
  intro y. destruct (Pos.eq_dec y x) as [->|Hneq].
  - rewrite !live_seed_row_set_same. cbn [fst snd].
    destruct (Hvalid x) as [Hdup Hseen]. split.
    + constructor; [intro Hin; apply Hseen in Hin; congruence|exact Hdup].
    + intro m. rewrite live_member_set, Hseen. split.
      * intros [Heq|Hin]; [left; symmetry; now apply Hinj|now right].
      * intros [Heq|Hin]; [left; now subst|now right].
  - rewrite !live_seed_row_set_other by exact Hneq.
    exact (Hvalid y).
Qed.

Lemma live_seed_add_row : forall A (encode : A -> positive) table n x,
  live_seed_valid encode table -> forall m y,
  In m (snd (live_seed_row (live_seed encode n x table) y)) <->
    (y = x /\ m = n) \/ In m (snd (live_seed_row table y)).
Proof.
  intros A encode table n x Hvalid m y. unfold live_seed.
  change (In m (snd (live_seed_row
    (if live_member (encode n) (fst (live_seed_row table x)) then table else
      PTrieCode.set x
        (PTrieCode.set (encode n) tt (fst (live_seed_row table x)),
          n :: snd (live_seed_row table x)) table) y)) <->
    (y = x /\ m = n) \/ In m (snd (live_seed_row table y))).
  destruct (live_member (encode n) (fst (live_seed_row table x))) eqn:Hn.
  - apply (proj2 (Hvalid x)) in Hn. split; [now right|].
    intros [[-> ->]|Hin]; assumption.
  - destruct (Pos.eq_dec y x) as [->|Hneq].
    + rewrite live_seed_row_set_same; cbn [snd In]. intuition congruence.
    + rewrite live_seed_row_set_other by exact Hneq. tauto.
Qed.

Lemma live_seed_fold_valid : forall A (encode : A -> positive),
  (forall a b, encode a = encode b -> a = b) -> forall xs table n,
  live_seed_valid encode table ->
  live_seed_valid encode (fold_right (live_seed encode n) table xs).
Proof.
  intros A encode Hinj xs; induction xs as [|x rest IH]; intros table n Hvalid; cbn;
    [exact Hvalid|apply live_seed_valid_add; [exact Hinj|now apply IH]].
Qed.

Lemma live_seed_fold_row : forall A (encode : A -> positive),
  (forall a b, encode a = encode b -> a = b) -> forall xs table n,
  live_seed_valid encode table -> forall m x,
  In m (snd (live_seed_row (fold_right (live_seed encode n) table xs) x)) <->
    (In x xs /\ m = n) \/ In m (snd (live_seed_row table x)).
Proof.
  intros A encode Hinj xs; induction xs as [|y rest IH]; intros table n Hvalid m x; cbn.
  - tauto.
  - rewrite live_seed_add_row by (apply live_seed_fold_valid; assumption).
    rewrite IH by exact Hvalid. cbn. intuition congruence.
Qed.

Lemma live_seed_batch_valid : forall A B (encode : A -> positive),
  (forall a b, encode a = encode b -> a = b) -> forall (point : B -> A) values items table,
  live_seed_valid encode table ->
  live_seed_valid encode (live_seed_batch encode point values items table).
Proof.
  intros A B encode Hinj point values items; induction items as [|item rest IH];
    intros table Hvalid; cbn [live_seed_batch fold_right].
  - exact Hvalid.
  - apply live_seed_fold_valid; [exact Hinj|now apply IH].
Qed.

Lemma live_seed_batch_row : forall A B (encode : A -> positive),
  (forall a b, encode a = encode b -> a = b) -> forall (point : B -> A) values items table,
  live_seed_valid encode table -> forall n x,
  In n (snd (live_seed_row (live_seed_batch encode point values items table) x)) <->
    (exists item, In item items /\ point item = n /\ In x (values item)) \/
      In n (snd (live_seed_row table x)).
Proof.
  intros A B encode Hinj point values items; induction items as [|item rest IH];
    intros table Hvalid n x; cbn [live_seed_batch fold_right].
  - split; [now right|intros [[item [Hin _]]|Hin]; [contradiction|assumption]].
  - fold (live_seed_batch encode point values rest table).
    rewrite live_seed_fold_row by (try exact Hinj; apply live_seed_batch_valid; assumption).
    rewrite IH by exact Hvalid. split.
    + intros [[Hx Hn]|[[other [Hin [Hpoint Hx]]]|Hin]].
      * left; exists item; split; [now left|split; [now symmetry|exact Hx]].
      * left; exists other; split; [now right|now split].
      * now right.
    + intros [[other [[Heq|Hin] [Hpoint Hx]]]|Hin].
      * subst other; left; split; [exact Hx|now symmetry].
      * right; left; exists other; now repeat split.
      * now right; right.
Qed.

Lemma live_intersection_spec : forall defs old x,
  live_member x (live_intersection defs old) = true <->
    In x defs /\ match old with None => True | Some row => live_member x row = true end.
Proof.
  intros defs; induction defs as [|y rest IH]; intros old x.
  - cbn [live_intersection]. unfold live_member; rewrite PTrie.get_empty; cbn.
    split; [discriminate|tauto].
  - cbn [live_intersection]. destruct old as [row|].
    + destruct (live_member y row) eqn:Hy.
      * rewrite live_member_set, IH. cbn. intuition congruence.
      * rewrite IH. cbn. intuition congruence.
    + rewrite live_member_set, IH. cbn. intuition congruence.
Qed.

Lemma live_kill_row_add_same : forall table src dst defs,
  live_kill_row (live_kill_add src dst defs table) src dst =
    Some (live_intersection defs (live_kill_row table src dst)).
Proof.
  intros table src dst defs. unfold live_kill_add, live_kill_row.
  rewrite PTrie.get_set_same, PTrie.get_set_same.
  destruct (trie_get dst table); [reflexivity|]. rewrite PTrie.get_empty; reflexivity.
Qed.

Lemma live_kill_row_add_other : forall table src dst defs query_src query_dst,
  query_src <> src \/ query_dst <> dst ->
  live_kill_row (live_kill_add src dst defs table) query_src query_dst =
    live_kill_row table query_src query_dst.
Proof.
  intros table src dst defs query_src query_dst Hother.
  unfold live_kill_add, live_kill_row.
  destruct (Pos.eq_dec query_dst dst) as [->|Hdst].
  - rewrite PTrie.get_set_same, PTrie.get_set_other by tauto.
    destruct (trie_get dst table); [reflexivity|]. apply PTrie.get_empty.
  - rewrite PTrie.get_set_other by exact Hdst. reflexivity.
Qed.

Lemma live_list_all_or_bad : forall A (test : A -> Prop),
  (forall x, {test x} + {~ test x}) -> forall xs,
  (forall x, In x xs -> test x) \/ exists x, In x xs /\ ~ test x.
Proof.
  intros A test Hdec xs; induction xs as [|x rest IH].
  - left; intros y Hin; contradiction.
  - destruct (Hdec x) as [Hx|Hx].
    + destruct IH as [Hall|[y [Hin Hbad]]].
      * left; intros y [->|Hin]; [exact Hx|now apply Hall].
      * right; exists y; split; [now right|exact Hbad].
    + right; exists x; split; [now left|exact Hx].
Qed.

Lemma live_pairs_in : forall A (xs : list positive) (rows : positive -> list A) n x,
  In (n, x) (flat_map (fun y => map (fun m => (m, y)) (rows y)) xs) <->
    In x xs /\ In n (rows x).
Proof.
  intros A xs rows n x. rewrite in_flat_map. split.
  - intros [y [Hy Hin]]. apply in_map_iff in Hin. destruct Hin as [m [Heq Hm]].
    injection Heq as -> ->. now split.
  - intros [Hx Hn]. exists x; split; [exact Hx|].
    apply in_map_iff. exists n; now split.
Qed.

Lemma live_nodup_append : forall A (left right : list A),
  NoDup left -> NoDup right -> (forall x, In x left -> ~ In x right) -> NoDup (left ++ right).
Proof.
  intros A left right Hleft; induction Hleft as [|x rest Hfresh Hrest IH];
    intros Hright Hdisjoint; cbn; [exact Hright|].
  constructor.
  - rewrite in_app_iff. intros [Hin|Hin]; [now apply Hfresh|now apply (Hdisjoint x (or_introl eq_refl))].
  - apply IH; [exact Hright|intros y Hin; apply Hdisjoint; now right].
Qed.

Lemma live_pairs_nodup : forall A xs (rows : positive -> list A),
  NoDup xs -> (forall x, NoDup (rows x)) ->
  NoDup (flat_map (fun x => map (fun n => (n, x)) (rows x)) xs).
Proof.
  intros A xs rows Hxs Hrows; induction Hxs as [|x rest Hfresh Hrest IH]; cbn;
    [constructor|].
  apply live_nodup_append; [|exact IH|].
  - induction (Hrows x) as [|n ns Hn Hns IHns]; cbn; [constructor|].
    constructor; [|exact IHns]. intro Hin. apply in_map_iff in Hin.
    destruct Hin as [m [Heq Hm]]. injection Heq as ->. now apply Hn.
  - intros [n y] Hin Htail. apply in_map_iff in Hin.
    destruct Hin as [m [Heq Hm]]. injection Heq as -> ->.
    apply live_pairs_in in Htail. apply Hfresh; tauto.
Qed.

Lemma live_index_set_same : forall A table key (row : list A),
  index_row (PTrieCode.set key row table) key = row.
Proof.
  intros A table key row; unfold index_row; now rewrite PTrie.get_set_same.
Qed.

Lemma live_index_set_other : forall A table key query (row : list A),
  query <> key -> index_row (PTrieCode.set key row table) query = index_row table query.
Proof.
  intros A table key query row Hneq; unfold index_row.
  now rewrite PTrie.get_set_other by exact Hneq.
Qed.

Definition live_rows_mass (bs : list positive) (rows : ptrie (list positive)) : nat :=
  fold_right (fun b n => length (index_row rows b) + n) 0 bs.

Lemma live_rows_mass_empty : forall bs, live_rows_mass bs Empty = 0.
Proof.
  intro bs; induction bs as [|b rest IH]; [reflexivity|].
  change (length (index_row (@Empty (list positive)) b) + live_rows_mass rest Empty = 0).
  unfold index_row at 1; rewrite PTrie.get_empty; cbn. exact IH.
Qed.

Lemma live_rows_mass_other : forall bs rows b row, ~ In b bs ->
  live_rows_mass bs (PTrieCode.set b row rows) = live_rows_mass bs rows.
Proof.
  intros bs; induction bs as [|a rest IH]; intros rows b row Hfresh;
    cbn [live_rows_mass fold_right]; [reflexivity|].
  fold (live_rows_mass rest (PTrieCode.set b row rows)).
  fold (live_rows_mass rest rows).
  rewrite live_index_set_other by (intro Heq; apply Hfresh; now left).
  rewrite IH by (intro Hin; apply Hfresh; now right). reflexivity.
Qed.

Lemma live_rows_mass_add : forall bs rows b x, NoDup bs ->
  live_rows_mass bs (PTrieCode.set b (x :: index_row rows b) rows) <=
    live_rows_mass bs rows + 1.
Proof.
  intros bs rows b x Hdup; induction Hdup as [|a rest Hfresh Hdup IH];
    cbn [live_rows_mass fold_right]; [lia|].
  fold (live_rows_mass rest (PTrieCode.set b (x :: index_row rows b) rows)).
  fold (live_rows_mass rest rows).
  destruct (Pos.eq_dec a b) as [->|Hneq].
  - rewrite live_index_set_same, live_rows_mass_other by exact Hfresh. cbn; lia.
  - rewrite live_index_set_other by exact Hneq. lia.
Qed.

Lemma live_indicator_absent : forall xs x amount, ~ In x xs ->
  fold_right (fun y acc => if Pos.eqb x y then amount + acc else acc) 0 xs = 0.
Proof.
  intros xs; induction xs as [|y rest IH]; intros x amount Hfresh; cbn; [reflexivity|].
  destruct (Pos.eqb x y) eqn:Heq.
  - apply Pos.eqb_eq in Heq. subst y. exfalso; apply Hfresh; now left.
  - apply IH. intro Hin; apply Hfresh; now right.
Qed.

Lemma live_indicator_once : forall xs x amount, NoDup xs -> In x xs ->
  fold_right (fun y acc => if Pos.eqb x y then amount + acc else acc) 0 xs = amount.
Proof.
  intros xs x amount Hdup; induction Hdup as [|y rest Hfresh Hdup IH]; intro Hin;
    [contradiction|]. cbn. destruct Hin as [->|Hin].
  - rewrite Pos.eqb_refl, live_indicator_absent by exact Hfresh. lia.
  - destruct (Pos.eqb x y) eqn:Heq.
    + apply Pos.eqb_eq in Heq. subst y; contradiction.
    + now apply IH.
Qed.

Lemma live_weighted_cons : forall A (cost : A * positive -> nat) rows pair xs,
  fold_right (fun x acc =>
    fold_right (fun item n => cost item + n) 0
      (filter (fun item => Pos.eqb (snd item) x) (pair :: rows)) + acc) 0 xs =
  fold_right (fun x acc => if Pos.eqb (snd pair) x then cost pair + acc else acc) 0 xs +
  fold_right (fun x acc =>
    fold_right (fun item n => cost item + n) 0
      (filter (fun item => Pos.eqb (snd item) x) rows) + acc) 0 xs.
Proof.
  intros A cost rows pair xs; induction xs as [|x rest IH]; cbn [fold_right filter]; [lia|].
  cbn [filter] in IH.
  destruct (Pos.eqb (snd pair) x); cbn [fold_right]; lia.
Qed.

Lemma live_weighted_partition : forall A (cost : A * positive -> nat) rows xs,
  NoDup xs -> (forall pair, In pair rows -> In (snd pair) xs) ->
  fold_right (fun x acc =>
    fold_right (fun pair n => cost pair + n) 0
      (filter (fun pair => Pos.eqb (snd pair) x) rows) + acc) 0 xs =
  fold_right (fun pair n => cost pair + n) 0 rows.
Proof.
  intros A cost rows; induction rows as [|pair rest IH]; intros xs Hdup Hcover.
  - induction xs as [|x tail IHxs]; cbn; [reflexivity|]. apply IHxs.
    + now inversion Hdup.
    + intros item Hin; contradiction.
  - rewrite live_weighted_cons, live_indicator_once by (try exact Hdup; apply Hcover; now left).
    rewrite IH by (try exact Hdup; intros item Hin; apply Hcover; now right).
    reflexivity.
Qed.

Lemma live_weighted_length : forall A (extra : A -> nat) xs,
  length xs <= fold_right (fun item n => 1 + extra item + n) 0 xs.
Proof.
  intros A extra xs; induction xs as [|item rest IH]; cbn in *; lia.
Qed.

Definition live_pair_member (table : ptrie (ptrie unit)) (x edge : positive) : bool :=
  match trie_get x table with None => false | Some row => live_member edge row end.
TimeFun live_pair_member.

Definition live_pair_insert (x edge : positive) (table : ptrie (ptrie unit))
    : ptrie (ptrie unit) :=
  let row := match trie_get x table with None => Empty | Some row => row end in
  PTrieCode.set x (PTrieCode.set edge tt row) table.
TimeFun live_pair_insert.

Definition live_pair_batch (edge : positive) (xs : list positive)
    (table : ptrie (ptrie unit)) : ptrie (ptrie unit) :=
  fold_right (fun x acc => live_pair_insert x edge acc) table xs.
TimeFun live_pair_batch.

Lemma live_pair_member_spec : forall table x edge,
  live_pair_member table x edge = true <->
    exists row, trie_get x table = Some row /\ trie_get edge row = Some tt.
Proof.
  intros table x edge. unfold live_pair_member.
  destruct (trie_get x table) as [row|] eqn:Hrow.
  - rewrite live_member_spec. split; [intro He; exists row; auto|].
    intros [other [Heq He]]. injection Heq as <-; exact He.
  - split; [discriminate|intros [row [Heq _]]; discriminate].
Qed.

Lemma live_pair_insert_spec : forall table x edge query other,
  live_pair_member (live_pair_insert x edge table) query other = true <->
    (query = x /\ other = edge) \/ live_pair_member table query other = true.
Proof.
  intros table x edge query other. unfold live_pair_insert, live_pair_member at 1.
  destruct (Pos.eq_dec query x) as [->|Hneq].
  - rewrite PTrie.get_set_same, live_member_set.
    unfold live_pair_member. destruct (trie_get x table) as [row|]; cbn [fst snd].
    + tauto.
    + unfold live_member; rewrite PTrie.get_empty. split; intros H; [tauto|].
      destruct H as [[_ Heq]|Hbad]; [now left|discriminate].
  - rewrite PTrie.get_set_other by exact Hneq.
    change (live_pair_member table query other = true <->
      (query = x /\ other = edge) \/ live_pair_member table query other = true).
    tauto.
Qed.

Lemma live_pair_batch_spec : forall xs table x edge query,
  live_pair_member (live_pair_batch edge xs table) x query = true <->
    (In x xs /\ query = edge) \/ live_pair_member table x query = true.
Proof.
  intros xs; induction xs as [|y rest IH]; intros table x edge query.
  - cbn [live_pair_batch fold_right In]. tauto.
  - change (live_pair_member (live_pair_insert y edge (live_pair_batch edge rest table))
      x query = true <->
      (In x (y :: rest) /\ query = edge) \/ live_pair_member table x query = true).
    rewrite live_pair_insert_spec, IH. cbn. intuition congruence.
Qed.

Lemma live_pair_index_spec : forall A (encode : A -> positive) defs items x edge,
  live_pair_member
    (fold_right (fun item acc => live_pair_batch (encode item) (defs item) acc) Empty items)
    x edge = true <->
    exists item, In item items /\ In x (defs item) /\ edge = encode item.
Proof.
  intros A encode defs items; induction items as [|item rest IH]; intros x edge;
    cbn [fold_right].
  - unfold live_pair_member. rewrite PTrie.get_empty. split; [discriminate|].
    intros [other [Hin _]]; contradiction.
  - rewrite live_pair_batch_spec, IH. split.
    + intros [[Hx Heq]|[other [Hin Hrest]]].
      * exists item; split; [now left|now split].
      * exists other; split; [now right|exact Hrest].
    + intros [other [[Heq|Hin] Hrest]].
      * subst other; now left.
      * right; exists other; auto.
Qed.

Module LiveCode (O : OPS)
    (P : TYPE with Definition t := func positive O.K O.G)
    (Q : TYPE) (R : LANG_PREPARE_OPS O Q)
    (BE E : TYPE) (N : KEY_OPS)
    (BC : CFG_INDEXED_OPS Q PosKeyCode BE) (C : CFG_INDEXED_OPS Q N E)
    (U : VARS_OPS Q N E C PosKeyCode)
    (SP : SSA_POINTS_OPS Q PosKeyCode BE BC N E C PosKeyCode U)
    <: LIVE_OPS O P Q R BE E N BC C U SP.
  Definition seed_table (q : Q.t) : ptrie (ptrie unit * list N.t) :=
    live_seed_batch N.encode (fun n => n) (U.exits q) (C.nodes q)
      (live_seed_batch N.encode (C.src q) (U.uses q) (C.edges q) Empty).

  Definition seed_index (q : Q.t) : ptrie (list N.t) :=
    PTrieCode.map snd (seed_table q).

  Definition reverse_index (q : Q.t) (es : list E.t) : ptrie (ptrie (ptrie unit)) :=
    fold_right (fun e acc =>
      live_kill_add (N.encode (C.src q e)) (N.encode (C.dst q e)) (U.defs q e) acc)
      Empty es.

  Definition reverse_kills (q : Q.t) : ptrie (ptrie (ptrie unit)) :=
    reverse_index q (C.edges q).

  Definition add_predecessors (q : Q.t) (kills : ptrie (ptrie (ptrie unit)))
      (x : positive) (n : N.t) (es : list E.t) (st : live_state N.t) : live_state N.t :=
    fold_right (fun e acc =>
      let pred := C.src q e in
      if live_killed kills (N.encode pred) (N.encode n) x then acc else
        live_discover N.encode pred acc) st es.

  Fixpoint explore_fuel (fuel : nat) (q : Q.t) (kills : ptrie (ptrie (ptrie unit)))
      (x : positive) (st : live_state N.t) : live_state N.t :=
    match fuel with
    | 0 => st
    | S rest =>
      match live_todo st with
      | [] => st
      | n :: pending =>
        explore_fuel rest q kills x
          (add_predecessors q kills x n (C.inc q n)
            {| live_seen := live_seen st; live_todo := pending; live_done := live_done st |})
      end
    end.

  Definition search (fuel : nat) (q : Q.t) (seeds : ptrie (list N.t))
      (kills : ptrie (ptrie (ptrie unit))) (x : positive) : list N.t :=
    live_done (explore_fuel fuel q kills x (live_initial N.encode (index_row seeds x))).

  Definition block_index (bs : list positive) : ptrie positive :=
    fold_right (fun b table => PTrieCode.set b b table) Empty bs.

  Definition group_point (q : Q.t) (listed : ptrie positive) (x : positive)
      (n : N.t) (rows : ptrie (list positive)) : ptrie (list positive) :=
    match live_lookup (SP.block_of_point q n) listed with
    | None => rows
    | Some b =>
      if N.eqb n (C.src q (SP.parameter_edge q b)) then
        PTrieCode.set b (x :: index_row rows b) rows
      else rows
    end.

  Definition live_in (p : P.t) : list (positive * list positive) :=
    let q := R.prepare p in
    let fuel := length (C.nodes q) in
    let seeds := seed_index q in
    let kills := reverse_kills q in
    let bs := BC.nodes q in
    let listed := block_index bs in
    let rows := fold_right (fun x acc =>
      fold_right (group_point q listed x) acc (search fuel q seeds kills x))
      Empty (U.universe q) in
    map (fun b => (b, index_row rows b)) bs.
End LiveCode.

Module Live (O : OPS)
    (P : TYPE with Definition t := func positive O.K O.G)
    (Q : TYPE) (R : LANG_PREPARE_OPS O Q)
    (BE E : TYPE) (N : KEY)
    (BC : CFG Q PosKey BE) (C : CFG Q N E) (U : VARS Q N E C PosKey)
    (SP : SSA_POINTS Q PosKey BE BC N E C PosKey U)
    <: LIVE O P Q R BE E N BC C U SP.
  Include LiveCode O P Q R BE E N BC C U SP.

  Lemma seed_table_valid : forall q, live_seed_valid N.encode (seed_table q).
  Proof.
    intro q. unfold seed_table. apply live_seed_batch_valid; [exact N.encode_inj|].
    apply live_seed_batch_valid; [exact N.encode_inj|apply live_seed_empty].
  Qed.

  Lemma seed_index_row : forall q x,
    index_row (seed_index q) x = snd (live_seed_row (seed_table q) x).
  Proof.
    intros q x. unfold seed_index, index_row, live_seed_row.
    rewrite PTrie.get_map. unfold PTrie.get.
    destruct (trie_get x (seed_table q)); reflexivity.
  Qed.

  Lemma seed_index_spec : forall q x n,
    In n (index_row (seed_index q) x) <->
      (In n (C.nodes q) /\ In x (U.exits q n)) \/
      exists e, In e (C.edges q) /\ C.src q e = n /\ In x (U.uses q e).
  Proof.
    intros q x n. rewrite seed_index_row. unfold seed_table.
    rewrite live_seed_batch_row by
      (first [exact N.encode_inj|apply live_seed_batch_valid;
        [exact N.encode_inj|apply live_seed_empty]]).
    rewrite live_seed_batch_row by (first [exact N.encode_inj|apply live_seed_empty]).
    unfold live_seed_row. rewrite PTrie.get_empty. cbn.
    split.
    - intros [[m [Hm [-> Hx]]]|[Hedge|[]]]; [left; now split|now right].
    - intros [[Hn Hx]|Hedge]; [left; exists n; auto|right; now left].
  Qed.

  Lemma seed_index_nodup : forall q x, NoDup (index_row (seed_index q) x).
  Proof.
    intros q x. rewrite seed_index_row. exact (proj1 (seed_table_valid q x)).
  Qed.

  Lemma seed_index_live : forall q x n, C.wf q ->
    In n (index_row (seed_index q) x) ->
    In n (C.nodes q) /\ In x (U.universe q) /\
      point_live (C.nodes q) (C.out q) (C.dst q) (U.uses q) (U.defs q) (U.exits q) x n.
  Proof.
    intros q x n Hwf Hin. apply seed_index_spec in Hin.
    destruct Hin as [[Hn Hx]|[e [He [<- Hx]]]].
    - split; [exact Hn|]. split.
      + apply U.universe_spec. right. exists n; now split.
      + now apply Point_live_exit.
    - split; [exact (proj1 (C.edges_nodes q e Hwf He))|]. split.
      + apply U.universe_spec. left. exists e; split; [exact He|now left].
      + apply Point_live_use with e; [apply C.out_spec; auto|exact Hx].
  Qed.

  Definition node_eq_dec (a b : N.t) : {a = b} + {a <> b}.
  Proof.
    destruct (N.eqb_spec a b); [now left|now right].
  Defined.

  Lemma reverse_index_spec : forall q es a b,
    (live_kill_row (reverse_index q es) (N.encode a) (N.encode b) = None <->
      ~ exists e, In e es /\ C.src q e = a /\ C.dst q e = b) /\
    forall row, live_kill_row (reverse_index q es) (N.encode a) (N.encode b) = Some row ->
      forall x, live_member x row = true <->
        forall e, In e es -> C.src q e = a -> C.dst q e = b -> In x (U.defs q e).
  Proof.
    intros q es; induction es as [|e rest IH]; intros a b.
    - unfold reverse_index, live_kill_row; cbn. rewrite PTrie.get_empty.
      split; [split; [intros _ [f [Hin _]]; contradiction|reflexivity]|discriminate].
    - cbn [reverse_index fold_right]. fold (reverse_index q rest).
      destruct (node_eq_dec a (C.src q e)) as [->|Hsrc];
        destruct (node_eq_dec b (C.dst q e)) as [->|Hdst].
      + rewrite live_kill_row_add_same. split.
        * split; [discriminate|]. intro Hnone; exfalso; apply Hnone.
          exists e; split; [now left|split; reflexivity].
        * intros row Hrow x. injection Hrow as <-. rewrite live_intersection_spec.
          specialize (IH (C.src q e) (C.dst q e)).
          destruct (live_kill_row (reverse_index q rest) (N.encode (C.src q e))
            (N.encode (C.dst q e))) as [old|] eqn:Hold.
          -- rewrite (proj2 IH old eq_refl). cbn. split.
             ++ intros [Hx Hall] f [->|Hin] Hs Hd; [exact Hx|now apply Hall].
             ++ intro Hall; split; [apply Hall; auto|intros f Hin; apply Hall; now right].
          -- cbn. split.
             ++ intros [Hx _] f [->|Hin] Hs Hd; [exact Hx|].
                exfalso. apply (proj1 (proj1 IH) eq_refl). exists f; auto.
             ++ intro Hall; split; [apply Hall; auto|exact I].
      + rewrite live_kill_row_add_other by (right; intro Heq; apply Hdst, N.encode_inj, Heq).
        specialize (IH (C.src q e) b). split.
        * rewrite (proj1 IH). cbn. split.
          -- intros Hnone [f [[Heq|Hin] [Hs Hd]]].
             ++ subst f; congruence.
             ++ apply Hnone; exists f; auto.
          -- intros Hnone [f [Hin Hends]]. apply Hnone; exists f; auto.
        * intros row Hrow x. rewrite (proj2 IH row Hrow). cbn. split.
          -- intros Hall f [->|Hin] Hs Hd; [exfalso; apply Hdst; symmetry; exact Hd|now apply Hall].
          -- intros Hall f Hin; apply Hall; now right.
      + rewrite live_kill_row_add_other by (left; intro Heq; apply Hsrc, N.encode_inj, Heq).
        specialize (IH a (C.dst q e)). split.
        * rewrite (proj1 IH). cbn. split.
          -- intros Hnone [f [[Heq|Hin] [Hs Hd]]].
             ++ subst f; congruence.
             ++ apply Hnone; exists f; auto.
          -- intros Hnone [f [Hin Hends]]. apply Hnone; exists f; auto.
        * intros row Hrow x. rewrite (proj2 IH row Hrow). cbn. split.
          -- intros Hall f [->|Hin] Hs Hd; [exfalso; apply Hsrc; symmetry; exact Hs|now apply Hall].
          -- intros Hall f Hin; apply Hall; now right.
      + rewrite live_kill_row_add_other by (left; intro Heq; apply Hsrc, N.encode_inj, Heq).
        specialize (IH a b). split.
        * rewrite (proj1 IH). cbn. split.
          -- intros Hnone [f [[Heq|Hin] [Hs Hd]]].
             ++ subst f; congruence.
             ++ apply Hnone; exists f; auto.
          -- intros Hnone [f [Hin Hends]]. apply Hnone; exists f; auto.
        * intros row Hrow x. rewrite (proj2 IH row Hrow). cbn. split.
          -- intros Hall f [->|Hin] Hs Hd; [exfalso; apply Hsrc; symmetry; exact Hs|now apply Hall].
          -- intros Hall f Hin; apply Hall; now right.
  Qed.

  Lemma reverse_kills_clear : forall q e x, In e (C.edges q) ->
    ~ In x (U.defs q e) ->
    live_killed (reverse_kills q) (N.encode (C.src q e)) (N.encode (C.dst q e)) x = false.
  Proof.
    intros q e x He Hnot. unfold live_killed, reverse_kills.
    destruct (live_kill_row (reverse_index q (C.edges q))
      (N.encode (C.src q e)) (N.encode (C.dst q e))) as [row|] eqn:Hrow; [|reflexivity].
    destruct (live_member x row) eqn:Hx; [|reflexivity]. exfalso. apply Hnot.
    apply (proj1 (proj2 (reverse_index_spec q (C.edges q) (C.src q e) (C.dst q e))
      row Hrow x) Hx e He); reflexivity.
  Qed.

  Lemma reverse_kills_cause : forall q e x, In e (C.edges q) ->
    live_killed (reverse_kills q) (N.encode (C.src q e)) (N.encode (C.dst q e)) x = false ->
    exists other, In other (C.edges q) /\ C.src q other = C.src q e /\
      C.dst q other = C.dst q e /\ ~ In x (U.defs q other).
  Proof.
    intros q e x He Hclear.
    destruct (reverse_index_spec q (C.edges q) (C.src q e) (C.dst q e)) as [Hnone Hall].
    unfold live_killed, reverse_kills in Hclear.
    destruct (live_kill_row (reverse_index q (C.edges q))
      (N.encode (C.src q e)) (N.encode (C.dst q e))) as [row|] eqn:Hrow.
    - assert (Hdec : forall other,
        {C.src q other = C.src q e -> C.dst q other = C.dst q e -> In x (U.defs q other)} +
        {~ (C.src q other = C.src q e -> C.dst q other = C.dst q e -> In x (U.defs q other))}).
      { intro other. destruct (node_eq_dec (C.src q other) (C.src q e)),
          (node_eq_dec (C.dst q other) (C.dst q e)), (in_dec Pos.eq_dec x (U.defs q other));
          [now left|right; tauto|now left|now left|now left|now left|now left|now left]. }
      destruct (live_list_all_or_bad _ _ Hdec (C.edges q)) as [Hdef|[other [Hin Hbad]]].
      + apply (proj2 (Hall row eq_refl x)) in Hdef. congruence.
      + exists other. destruct (node_eq_dec (C.src q other) (C.src q e)),
          (node_eq_dec (C.dst q other) (C.dst q e)); intuition.
    - exfalso. apply (proj1 Hnone eq_refl). exists e; auto.
  Qed.

  Lemma live_predecessor : forall q x n e, C.wf q -> In e (C.inc q n) ->
    point_live (C.nodes q) (C.out q) (C.dst q) (U.uses q) (U.defs q) (U.exits q) x n ->
    live_killed (reverse_kills q) (N.encode (C.src q e)) (N.encode n) x = false ->
    point_live (C.nodes q) (C.out q) (C.dst q) (U.uses q) (U.defs q) (U.exits q) x (C.src q e).
  Proof.
    intros q x n e Hwf He Hlive Hclear. apply C.inc_spec in He; [|exact Hwf].
    destruct He as [He Hdst]. rewrite <- Hdst in Hclear.
    destruct (reverse_kills_cause q e x He Hclear) as [other [Ho [Hsrc [Htarget Hnot]]]].
    apply Point_live_next with other.
    - apply C.out_spec; [exact Hwf|now split].
    - exact Hnot.
    - exact (proj2 (C.edges_nodes q other Hwf Ho)).
    - now rewrite Htarget, Hdst.
  Qed.

  Lemma add_predecessors_valid : forall q kills x n es st,
    live_valid N.encode st -> live_valid N.encode (add_predecessors q kills x n es st).
  Proof.
    intros q kills x n es; induction es as [|e rest IH]; intros st Hvalid;
      cbn [add_predecessors fold_right]; [exact Hvalid|].
    destruct (live_killed kills (N.encode (C.src q e)) (N.encode n) x).
    - now apply IH.
    - apply live_discover_valid; [exact N.encode_inj|now apply IH].
  Qed.

  Lemma add_predecessors_done : forall q kills x n es st,
    live_valid N.encode st -> forall m,
    In m (live_done (add_predecessors q kills x n es st)) <->
      In m (live_done st) \/ exists e, In e es /\
        live_killed kills (N.encode (C.src q e)) (N.encode n) x = false /\ C.src q e = m.
  Proof.
    intros q kills x n es; induction es as [|e rest IH]; intros st Hvalid m;
      cbn [add_predecessors fold_right].
    - split; [now left|intros [Hin|[e [Hin _]]]; [assumption|contradiction]].
    - fold (add_predecessors q kills x n rest st).
      destruct (live_killed kills (N.encode (C.src q e)) (N.encode n) x) eqn:He.
      + rewrite IH by exact Hvalid. split.
        * intros [Hin|[f [Hf Hrest]]]; [now left|].
          right; exists f; split; [now right|exact Hrest].
        * intros [Hin|[f [[->|Hf] [Hclear Hsrc]]]]; [now left|congruence|].
          right; exists f; now repeat split.
      + rewrite live_discover_done by (now apply add_predecessors_valid).
        rewrite IH by exact Hvalid. split.
        * intros [Heq|[Hin|[f [Hf Hrest]]]].
          -- right; exists e; split; [now left|split; [exact He|now symmetry]].
          -- now left.
          -- right; exists f; split; [now right|exact Hrest].
        * intros [Hin|[f [[->|Hf] [Hclear Hsrc]]]].
          -- now right; left.
          -- left; now symmetry.
          -- right; right; exists f; auto.
  Qed.

  Lemma add_predecessors_processed : forall q kills x n es st m,
    live_valid N.encode st ->
    In m (live_done (add_predecessors q kills x n es st)) ->
    ~ In m (live_todo (add_predecessors q kills x n es st)) ->
    In m (live_done st) /\ ~ In m (live_todo st).
  Proof.
    intros q kills x n es; induction es as [|e rest IH]; intros st m Hvalid Hdone Htodo.
    - now split.
    - cbn [add_predecessors fold_right] in Hdone, Htodo.
      fold (add_predecessors q kills x n rest st) in Hdone, Htodo.
      destruct (live_killed kills (N.encode (C.src q e)) (N.encode n) x);
        [now apply IH with (m := m)|].
      unfold live_discover in Hdone, Htodo.
      destruct (live_member (N.encode (C.src q e))
        (live_seen (add_predecessors q kills x n rest st))).
      + now apply IH with (m := m).
      + cbn in Hdone, Htodo. apply IH with (m := m); try assumption; tauto.
  Qed.

  Lemma add_predecessors_balance : forall q kills x n es st,
    length (live_done (add_predecessors q kills x n es st)) + length (live_todo st) =
      length (live_done st) + length (live_todo (add_predecessors q kills x n es st)).
  Proof.
    intros q kills x n es; induction es as [|e rest IH]; intro st;
      cbn [add_predecessors fold_right]; [lia|].
    fold (add_predecessors q kills x n rest st).
    destruct (live_killed kills (N.encode (C.src q e)) (N.encode n) x); [apply IH|].
    pose proof (live_discover_balance _ N.encode (add_predecessors q kills x n rest st)
      (C.src q e)). specialize (IH st). lia.
  Qed.

  Definition live_sound (q : Q.t) (x : positive) (st : live_state N.t) : Prop :=
    forall n, In n (live_done st) -> In n (C.nodes q) /\
      point_live (C.nodes q) (C.out q) (C.dst q) (U.uses q) (U.defs q) (U.exits q) x n.

  Definition live_ready (q : Q.t) (kills : ptrie (ptrie (ptrie unit)))
      (x : positive) (st : live_state N.t) : Prop :=
    forall n, In n (live_done st) -> ~ In n (live_todo st) -> forall e,
      In e (C.inc q n) -> live_killed kills (N.encode (C.src q e)) (N.encode n) x = false ->
      In (C.src q e) (live_done st).

  Lemma live_pop_valid : forall st n pending,
    live_valid N.encode st -> live_todo st = n :: pending ->
    live_valid N.encode
      {| live_seen := live_seen st; live_todo := pending; live_done := live_done st |}.
  Proof.
    intros st n pending [Hdone [Hseen [Htodo Hsub]]] Heq.
    split; [exact Hdone|]. split; [exact Hseen|]. cbn.
    rewrite Heq in Htodo, Hsub. inversion Htodo; subst.
    split; [assumption|intros m Hin; apply Hsub; now right].
  Qed.

  Lemma live_step_sound : forall q x st n pending, C.wf q ->
    live_valid N.encode st -> live_sound q x st -> live_todo st = n :: pending ->
    live_sound q x (add_predecessors q (reverse_kills q) x n (C.inc q n)
      {| live_seen := live_seen st; live_todo := pending; live_done := live_done st |}).
  Proof.
    intros q x st n pending Hwf Hvalid Hsound Htodo m Hin.
    apply add_predecessors_done in Hin; [|eapply live_pop_valid; eassumption].
    destruct Hin as [Hin|[e [He [Hclear <-]]]].
    - now apply Hsound.
    - split.
      + apply C.inc_spec in He; [|exact Hwf].
        exact (proj1 (C.edges_nodes q e Hwf (proj1 He))).
      + apply live_predecessor with n; try assumption.
        assert (Hn : In n (live_done st)).
        { apply (proj2 (proj2 (proj2 Hvalid))). rewrite Htodo; now left. }
        exact (proj2 (Hsound n Hn)).
  Qed.

  Lemma live_step_ready : forall q kills x st n pending,
    live_valid N.encode st -> live_ready q kills x st -> live_todo st = n :: pending ->
    live_ready q kills x (add_predecessors q kills x n (C.inc q n)
      {| live_seen := live_seen st; live_todo := pending; live_done := live_done st |}).
  Proof.
    intros q kills x st n pending Hvalid Hready Htodo m Hdone Hnot e He Hclear.
    assert (Hpop := live_pop_valid st n pending Hvalid Htodo).
    destruct (add_predecessors_processed q kills x n (C.inc q n) _ m Hpop Hdone Hnot)
      as [Hold Hpending]. cbn in Hold, Hpending.
    apply add_predecessors_done; [exact Hpop|].
    destruct (node_eq_dec m n) as [->|Hneq].
    - right; exists e; auto.
    - left. apply Hready with m; try assumption. rewrite Htodo; cbn. intuition congruence.
  Qed.

  Lemma explore_fuel_correct : forall fuel q x st, C.wf q ->
    live_valid N.encode st -> live_sound q x st -> live_ready q (reverse_kills q) x st ->
    length (C.nodes q) + length (live_todo st) <= length (live_done st) + fuel ->
    let result := explore_fuel fuel q (reverse_kills q) x st in
    live_valid N.encode result /\ live_sound q x result /\
      live_ready q (reverse_kills q) x result /\ live_todo result = [] /\
      incl (live_done st) (live_done result).
  Proof.
    induction fuel as [|fuel IH]; intros q x st Hwf Hvalid Hsound Hready Hbudget.
    - cbn [explore_fuel]. assert (Hlength : length (live_done st) <= length (C.nodes q)).
      { apply NoDup_incl_length; [exact (proj1 Hvalid)|].
        intros n Hin; exact (proj1 (Hsound n Hin)). }
      assert (Hempty : live_todo st = []) by (apply length_zero_iff_nil; lia).
      split; [exact Hvalid|]. split; [exact Hsound|]. split; [exact Hready|].
      split; [exact Hempty|apply incl_refl].
    - cbn [explore_fuel]. destruct (live_todo st) as [|n pending] eqn:Htodo.
      + split; [exact Hvalid|]. split; [exact Hsound|]. split; [exact Hready|].
        split; [exact Htodo|apply incl_refl].
      + set (popped := {| live_seen := live_seen st; live_todo := pending;
                         live_done := live_done st |}).
        set (next := add_predecessors q (reverse_kills q) x n (C.inc q n) popped).
        assert (Hpop : live_valid N.encode popped) by (eapply live_pop_valid; eassumption).
        assert (Hnext : live_valid N.encode next) by (now apply add_predecessors_valid).
        assert (Hnext_sound : live_sound q x next) by (eapply live_step_sound; eassumption).
        assert (Hnext_ready : live_ready q (reverse_kills q) x next)
          by (eapply live_step_ready; eassumption).
        assert (Hnext_budget : length (C.nodes q) + length (live_todo next) <=
          length (live_done next) + fuel).
        { pose proof (add_predecessors_balance q (reverse_kills q) x n (C.inc q n) popped)
            as Hbalance.
          fold next in Hbalance. unfold popped in Hbalance; cbn in Hbalance.
          cbn in Hbudget.
          lia. }
        destruct (IH q x next Hwf Hnext Hnext_sound Hnext_ready Hnext_budget)
          as [Hv [Hs [Hr [Ht Hsub]]]].
        split; [exact Hv|]. split; [exact Hs|]. split; [exact Hr|]. split; [exact Ht|].
        intros m Hin. apply Hsub. apply add_predecessors_done; [exact Hpop|now left].
  Qed.

  Lemma point_live_universe : forall q x n, C.wf q -> In n (C.nodes q) ->
    point_live (C.nodes q) (C.out q) (C.dst q) (U.uses q) (U.defs q) (U.exits q) x n ->
    In x (U.universe q).
  Proof.
    intros q x n Hwf Hnode Hlive; revert Hnode.
    induction Hlive as [n Hexit|n e Hout Huse|n e Hout Hnot Hdst Hlive IH]; intro Hnode.
    - apply U.universe_spec. right; exists n; now split.
    - apply U.universe_spec. left; exists e; split; [|now left].
      now apply (C.out_spec q n e Hwf) in Hout.
    - now apply IH.
  Qed.

  Lemma search_spec : forall q x, C.wf q ->
    NoDup (search (length (C.nodes q)) q (seed_index q) (reverse_kills q) x) /\ forall n,
      In n (search (length (C.nodes q)) q (seed_index q) (reverse_kills q) x) <->
      In n (C.nodes q) /\
        point_live (C.nodes q) (C.out q) (C.dst q) (U.uses q) (U.defs q) (U.exits q) x n.
  Proof.
    intros q x Hwf.
    set (initial := live_initial N.encode (index_row (seed_index q) x)).
    assert (Hvalid : live_valid N.encode initial) by
      (apply live_initial_valid; exact N.encode_inj).
    assert (Hsound : live_sound q x initial).
    { intros n Hin. apply live_initial_done in Hin; [|exact N.encode_inj].
      destruct (seed_index_live q x n Hwf Hin) as [Hn [_ Hlive]]; now split. }
    assert (Hready : live_ready q (reverse_kills q) x initial).
    { intros n Hin Hnot. exfalso. apply Hnot.
      unfold initial. rewrite live_initial_todo. exact Hin. }
    assert (Hbudget : length (C.nodes q) + length (live_todo initial) <=
      length (live_done initial) + length (C.nodes q)).
    { unfold initial. rewrite live_initial_todo. lia. }
    destruct (explore_fuel_correct (length (C.nodes q)) q x initial Hwf Hvalid Hsound Hready
      Hbudget) as [Hresult [Hlive [Hclosed [Hempty Hcontains]]]].
    split; [exact (proj1 Hresult)|]. intro n. split; [apply Hlive|].
    intros [Hnode Hn]; revert Hnode.
    induction Hn as [n Hexit|n e Hout Huse|n e Hout Hnot Hdst Hn IH]; intro Hnode.
    - apply Hcontains. apply live_initial_done; [exact N.encode_inj|].
      apply seed_index_spec. now left.
    - apply Hcontains. apply live_initial_done; [exact N.encode_inj|].
      apply seed_index_spec. right; exists e. apply C.out_spec in Hout; [|exact Hwf].
      tauto.
    - apply C.out_spec in Hout; [|exact Hwf]. destruct Hout as [He Hsrc].
      rewrite <- Hsrc. apply Hclosed with (C.dst q e); [now apply IH| | |].
      + rewrite Hempty. tauto.
      + apply C.inc_spec; auto.
      + now apply reverse_kills_clear.
  Qed.

  Lemma group_point_values : forall q listed x n rows allowed,
    In x allowed -> (forall b, incl (index_row rows b) allowed) ->
    forall b, incl (index_row (group_point q listed x n rows) b) allowed.
  Proof.
    intros q listed x n rows allowed Hx Hrows b. unfold group_point.
    destruct (live_lookup (SP.block_of_point q n) listed) as [target|]; [|apply Hrows].
    destruct (N.eqb n (C.src q (SP.parameter_edge q target))); [|apply Hrows].
    destruct (Pos.eq_dec b target) as [->|Hneq].
    - rewrite live_index_set_same. intros y [->|Hin]; [exact Hx|now apply (Hrows target)].
    - rewrite live_index_set_other by exact Hneq. apply Hrows.
  Qed.

  Lemma group_points_values : forall q listed x ns rows allowed,
    In x allowed -> (forall b, incl (index_row rows b) allowed) ->
    forall b, incl (index_row (fold_right (group_point q listed x) rows ns) b) allowed.
  Proof.
    intros q listed x ns; induction ns as [|n rest IH]; intros rows allowed Hx Hrows b;
      cbn; [apply Hrows|]. apply group_point_values; [exact Hx|now apply IH].
  Qed.

  Lemma group_point_mass : forall q listed x n rows bs, NoDup bs ->
    live_rows_mass bs (group_point q listed x n rows) <= live_rows_mass bs rows + 1.
  Proof.
    intros q listed x n rows bs Hdup. unfold group_point.
    destruct (live_lookup (SP.block_of_point q n) listed) as [target|]; [|lia].
    destruct (N.eqb n (C.src q (SP.parameter_edge q target))); [|lia].
    now apply live_rows_mass_add.
  Qed.

  Lemma group_points_mass : forall q listed x ns rows bs, NoDup bs ->
    live_rows_mass bs (fold_right (group_point q listed x) rows ns) <=
      live_rows_mass bs rows + length ns.
  Proof.
    intros q listed x ns; induction ns as [|n rest IH]; intros rows bs Hdup; cbn; [lia|].
    pose proof (group_point_mass q listed x n
      (fold_right (group_point q listed x) rows rest) bs Hdup).
    specialize (IH rows bs Hdup). lia.
  Qed.

  Lemma group_variables_values : forall q listed xs visits,
    forall b, incl (index_row (fold_right (fun x acc =>
      fold_right (group_point q listed x) acc (visits x)) Empty xs) b) xs.
  Proof.
    intros q listed xs visits; induction xs as [|x rest IH]; intro b; cbn.
    - unfold index_row; rewrite PTrie.get_empty. intros y Hin; contradiction.
    - apply group_points_values; [now left|].
      intros target y Hin; right; now apply (IH target).
  Qed.

  Lemma group_variables_mass : forall q listed xs visits bs, NoDup bs ->
    live_rows_mass bs (fold_right (fun x acc =>
      fold_right (group_point q listed x) acc (visits x)) Empty xs) <=
      length (flat_map (fun x => map (fun n => (n, x)) (visits x)) xs).
  Proof.
    intros q listed xs visits bs Hdup; induction xs as [|x rest IH]; cbn.
    - rewrite live_rows_mass_empty. lia.
    - rewrite length_app, length_map.
      pose proof (group_points_mass q listed x (visits x)
        (fold_right (fun y acc => fold_right (group_point q listed y) acc (visits y))
          Empty rest) bs Hdup). lia.
  Qed.
End Live.

Module LiveT (O : OPS)
    (P : TYPE with Definition t := func positive O.K O.G)
    (Q : TYPE) (R : LANG_PREPARE_T O Q)
    (BE E N : KEY_T)
    (BC : CFG_T Q PosKeyT BE) (C : CFG_T Q N E) (U : VARS_T Q N E C PosKeyT)
    (SP : SSA_POINTS_T Q PosKeyT BE BC N E C PosKeyT U)
    (PB : LANG_PRESENT_BUDGET O Q R BE E N BC C U SP)
    <: LIVE_ALL O P Q R BE E N BC C U SP PB.
  Include Live O P Q R BE E N BC C U SP.
  TimeFun seed_table.
  TimeFun seed_index.
  TimeFun reverse_index.
  TimeFun reverse_kills.
  TimeFun add_predecessors.
  TimeFun explore_fuel.
  TimeFun search.
  TimeFun block_index.
  TimeFun group_point.
  TimeFun live_in.
  Definition live_region (p : P.t) : list (N.t * positive) :=
    let q := R.prepare p in
    let fuel := length (C.nodes q) in
    let seeds := seed_index q in
    let kills := reverse_kills q in
    flat_map (fun x => map (fun n => (n, x)) (search fuel q seeds kills x)) (U.universe q).
  (** The cost region enumerates each live point/value pair exactly once. *)
  Lemma live_region_spec : forall p,
    NoDup (live_region p) /\ forall n x,
      (In (n, x) (live_region p) <-> In n (C.nodes (R.prepare p)) /\
        In x (U.universe (R.prepare p)) /\
        point_live (C.nodes (R.prepare p)) (C.out (R.prepare p)) (C.dst (R.prepare p))
          (U.uses (R.prepare p)) (U.defs (R.prepare p)) (U.exits (R.prepare p)) x n).
  Proof.
    intro p. unfold live_region.
    pose proof (proj2 (PB.prepared_wf p)) as Hwf. split.
    - apply live_pairs_nodup; [apply U.universe_nodup|]. intro x.
      exact (proj1 (search_spec (R.prepare p) x Hwf)).
    - intros n x. rewrite live_pairs_in, (proj2 (search_spec (R.prepare p) x Hwf) n).
      tauto.
  Qed.
  Definition live_size p := fold_right (fun pair n =>
    1 + length (C.inc (R.prepare p) (fst pair)) + n) 0 (live_region p).
  Definition rows_size (rows : list (positive * list positive)) :=
    fold_right (fun row n => 1 + length (snd row) + n) 0 rows.
  (** The producer emits at most one row entry per charged block and live pair. *)
  Lemma live_in_size : forall p,
    rows_size (live_in p) <= length (blocks _ _ _ p) + live_size p.
  Proof.
    intro p. unfold live_in.
    set (q := R.prepare p). set (bs := BC.nodes q).
    set (visits := search (length (C.nodes q)) q (seed_index q) (reverse_kills q)).
    set (rows := fold_right (fun x acc =>
      fold_right (group_point q (block_index bs) x) acc (visits x)) Empty (U.universe q)).
    assert (Hrows : forall ids table,
      rows_size (map (fun b => (b, index_row table b)) ids) =
        length ids + live_rows_mass ids table).
    { intros ids table; induction ids as [|b rest IH]; [reflexivity|].
      change (1 + length (index_row table b) +
        rows_size (map (fun id => (id, index_row table id)) rest) =
        S (length rest) + (length (index_row table b) + live_rows_mass rest table)).
      rewrite IH. lia. }
    rewrite Hrows.
    change (length bs + live_rows_mass bs rows <= length (blocks _ _ _ p) + live_size p).
    assert (Hmass : live_rows_mass bs rows <= length (live_region p)).
    { apply group_variables_mass. apply BC.nodes_nodup. exact (proj1 (PB.prepared_wf p)). }
    assert (Hregion : length (live_region p) <= live_size p).
    { unfold live_size. apply live_weighted_length. }
    pose proof (PB.block_nodes_le p) as Hblocks. unfold bs, q in *. lia.
  Qed.
  Definition c_live : N := 1. (* STUB *)
  (** Path exploration pays for syntax and live predecessor incidences. *)
  Lemma T_live_in_le : forall p,
    (T_live_in p <= c_live * N.of_nat (function_size p + live_size p + 1) *
      N.of_nat (function_width p + 1))%N.
  Proof. Admitted. (* STUB *)
  (** The producer has the published output-sensitive bit-cost bound. *)
  Lemma live_in_bigO : bigO (fun _ : P.t => True)
    (fun p => N.of_nat ((function_size p + live_size p + 1) * (function_width p + 1)))
    T_live_in.
  Proof. Admitted. (* STUB *)
  Definition use_index (q : Q.t) : ptrie (list N.t) := seed_index q.
  TimeFun use_index.
  Definition kill_index (q : Q.t) : ptrie (ptrie unit) :=
    fold_right (fun e rows =>
      fold_right (fun x acc =>
        let row := match trie_get x acc with Some m => m | None => Empty end in
        PTrieCode.set x (PTrieCode.set (E.encode e) tt row) acc) rows (U.defs q e))
      Empty (C.edges q).
  TimeFun kill_index.
  Definition plan_predecessors (q : Q.t) (kills : ptrie (ptrie unit)) (x : positive)
      (es : list E.t) (st : live_state N.t) : live_state N.t :=
    fold_right (fun e acc =>
      if live_pair_member kills x (E.encode e) then acc else
        live_discover N.encode (C.src q e) acc) st es.
  TimeFun plan_predecessors.

  Fixpoint plan_fuel (fuel : nat) (q : Q.t) (kills : ptrie (ptrie unit)) (x : positive)
      (st : live_state N.t) : live_state N.t :=
    match fuel with
    | 0 => st
    | S rest =>
      match live_todo st with
      | [] => st
      | n :: pending => plan_fuel rest q kills x
          (plan_predecessors q kills x (C.inc q n)
            {| live_seen := live_seen st; live_todo := pending; live_done := live_done st |})
      end
    end.
  TimeFun plan_fuel.

  Definition explore (q : Q.t) (seeds : ptrie (list N.t)) (kills : ptrie (ptrie unit))
      (x : positive) : list N.t :=
    live_done (plan_fuel (length (C.nodes q)) q kills x
      (live_initial N.encode (index_row seeds x))).
  TimeFun explore.
  Definition k_index : N := 1. (* STUB *)
  Definition k_explore : N := 1. (* STUB *)
  Definition k_rows : N := 1. (* STUB *)
  Definition visits p x := filter (fun pair => Pos.eqb (snd pair) x) (live_region p).
  Definition variable_work p x := fold_right (fun pair n =>
    1 + length (C.inc (R.prepare p) (fst pair)) + n) 0 (visits p x).
  Definition searched p x :=
    explore (R.prepare p) (use_index (R.prepare p)) (kill_index (R.prepare p)) x.
  (** Indexed use points of a variable are distinct charged live pairs. *)
  Lemma F0_use_index : forall p x,
    NoDup (index_row (use_index (R.prepare p)) x) /\
    forall n, In n (index_row (use_index (R.prepare p)) x) -> In (n, x) (live_region p).
  Proof.
    intros p x. split; [apply seed_index_nodup|]. intros n Hin.
    apply (proj2 (live_region_spec p) n x).
    apply seed_index_live; [exact (proj2 (PB.prepared_wf p))|exact Hin].
  Qed.
  (** The kill index answers, for a variable and a listed edge, whether the edge defines it. *)
  Lemma F0b_kill_index : forall p x e, In e (C.edges (R.prepare p)) ->
    ((exists m, trie_get x (kill_index (R.prepare p)) = Some m /\
      trie_get (E.encode e) m = Some tt) <-> In x (U.defs (R.prepare p) e)).
  Proof.
    intros p x e He. rewrite <- live_pair_member_spec.
    change (live_pair_member
      (fold_right (fun item acc => live_pair_batch (E.encode item)
        (U.defs (R.prepare p) item) acc) Empty (C.edges (R.prepare p))) x (E.encode e) = true
      <-> In x (U.defs (R.prepare p) e)).
    rewrite live_pair_index_spec. split.
    - intros [other [Hin [Hx Heq]]]. apply E.encode_inj in Heq. now subst other.
    - intro Hx. exists e; auto.
  Qed.
  Lemma plan_predecessors_valid : forall q kills x es st,
    live_valid N.encode st -> live_valid N.encode (plan_predecessors q kills x es st).
  Proof.
    intros q kills x es; induction es as [|e rest IH]; intros st Hvalid;
      cbn [plan_predecessors fold_right]; [exact Hvalid|].
    destruct (live_pair_member kills x (E.encode e)); [now apply IH|].
    apply live_discover_valid; [exact N.encode_inj|now apply IH].
  Qed.

  Lemma plan_fuel_valid : forall fuel q kills x st,
    live_valid N.encode st -> live_valid N.encode (plan_fuel fuel q kills x st).
  Proof.
    induction fuel as [|fuel IH]; intros q kills x st Hvalid; cbn [plan_fuel];
      [exact Hvalid|].
    destruct (live_todo st) as [|n pending] eqn:Htodo; [exact Hvalid|].
    apply IH, plan_predecessors_valid. eapply live_pop_valid; eassumption.
  Qed.

  Lemma plan_predecessors_sound : forall q kills x n es st, C.wf q ->
    (forall e, In e (C.edges q) ->
      (live_pair_member kills x (E.encode e) = true <-> In x (U.defs q e))) ->
    incl es (C.inc q n) ->
    point_live (C.nodes q) (C.out q) (C.dst q) (U.uses q) (U.defs q) (U.exits q) x n ->
    live_sound q x st -> live_sound q x (plan_predecessors q kills x es st).
  Proof.
    intros q kills x n es; induction es as [|e rest IH]; intros st Hwf Hkill Hinc Hlive Hsound;
      cbn [plan_predecessors fold_right]; [exact Hsound|].
    fold (plan_predecessors q kills x rest st).
    assert (Htail : live_sound q x (plan_predecessors q kills x rest st)).
    { apply IH; try assumption. intros edge Hin; apply Hinc; now right. }
    destruct (live_pair_member kills x (E.encode e)) eqn:Hclear; [exact Htail|].
    unfold live_discover. destruct (live_member (N.encode (C.src q e))
      (live_seen (plan_predecessors q kills x rest st))); [exact Htail|].
    intros m [<-|Hin]; [|now apply Htail].
    assert (He : In e (C.edges q) /\ C.dst q e = n).
    { apply C.inc_spec; [exact Hwf|apply Hinc; now left]. }
    split; [exact (proj1 (C.edges_nodes q e Hwf (proj1 He)))|].
    apply Point_live_next with e.
    - apply C.out_spec; [exact Hwf|]. split; [exact (proj1 He)|reflexivity].
    - intro Hdef. apply (proj2 (Hkill e (proj1 He))) in Hdef. congruence.
    - exact (proj2 (C.edges_nodes q e Hwf (proj1 He))).
    - now rewrite (proj2 He).
  Qed.

  Lemma plan_fuel_sound : forall fuel q kills x st, C.wf q ->
    (forall e, In e (C.edges q) ->
      (live_pair_member kills x (E.encode e) = true <-> In x (U.defs q e))) ->
    live_valid N.encode st -> live_sound q x st -> live_sound q x (plan_fuel fuel q kills x st).
  Proof.
    induction fuel as [|fuel IH]; intros q kills x st Hwf Hkill Hvalid Hsound;
      cbn [plan_fuel]; [exact Hsound|].
    destruct (live_todo st) as [|n pending] eqn:Htodo; [exact Hsound|].
    apply IH; try assumption.
    - apply plan_predecessors_valid. eapply live_pop_valid; eassumption.
    - apply plan_predecessors_sound with n;
        [exact Hwf|exact Hkill|apply incl_refl| |exact Hsound].
      assert (Hn : In n (live_done st)).
      { apply (proj2 (proj2 (proj2 Hvalid))). rewrite Htodo; now left. }
      exact (proj2 (Hsound n Hn)).
  Qed.

  (** Each per-variable search visits a point at most once. *)
  Lemma F1_explore_nodup : forall p x, NoDup (searched p x).
  Proof.
    intros p x. pose proof (plan_fuel_valid (length (C.nodes (R.prepare p)))
      (R.prepare p) (kill_index (R.prepare p)) x
      (live_initial N.encode (index_row (use_index (R.prepare p)) x))
      (live_initial_valid N.t N.encode N.encode_inj _)) as Hvalid.
    exact (proj1 Hvalid).
  Qed.
  (** Every visited search point belongs to its charged semantic region. *)
  Lemma F2_explore_region : forall p x n,
    In n (searched p x) -> In (n, x) (live_region p).
  Proof.
    intros p x n Hin. apply (proj2 (live_region_spec p) n x).
    assert (Hwf := proj2 (PB.prepared_wf p)).
    assert (Hsound : live_sound (R.prepare p) x
      (plan_fuel (length (C.nodes (R.prepare p))) (R.prepare p) (kill_index (R.prepare p)) x
        (live_initial N.encode (index_row (use_index (R.prepare p)) x)))).
    { apply plan_fuel_sound; [exact Hwf| | |].
      - intros e He. rewrite live_pair_member_spec. now apply F0b_kill_index.
      - apply live_initial_valid; exact N.encode_inj.
      - intros m Hm. apply live_initial_done in Hm; [|exact N.encode_inj].
        destruct (seed_index_live (R.prepare p) x m Hwf Hm) as [Hn [_ Hl]]; now split. }
    destruct (Hsound n Hin) as [Hn Hl]. split; [exact Hn|]. split; [|exact Hl].
    now apply point_live_universe with n.
  Qed.
  (** Deduplicated variables partition the total live-incidence budget. *)
  Lemma F3_partition : forall p,
    fold_right (fun x n => variable_work p x + n) 0 (U.universe (R.prepare p)) =
      live_size p.
  Proof.
    intro p. unfold variable_work, visits, live_size.
    apply live_weighted_partition; [apply U.universe_nodup|].
    intros [n x] Hin. apply (proj2 (live_region_spec p) n x) in Hin. tauto.
  Qed.
  (** Indexing reads each variable occurrence once at the syntax width. *)
  Lemma T0_use_index : forall p,
    (T_use_index (R.prepare p) <= k_index * N.of_nat (function_size p + 1) *
      N.of_nat (function_width p + 1))%N.
  Proof. Admitted. (* STUB *)
  (** The kill index reads each definition occurrence once at the syntax width. *)
  Lemma T0_kill_index : forall p,
    (T_kill_index (R.prepare p) <= k_index * N.of_nat (function_size p + 1) *
      N.of_nat (function_width p + 1))%N.
  Proof. Admitted. (* STUB *)
  (** A variable's search charges each visited point and incoming occurrence. *)
  Lemma T1_explore : forall p x, In x (U.universe (R.prepare p)) ->
    (T_explore (R.prepare p) (use_index (R.prepare p)) (kill_index (R.prepare p)) x <=
      k_explore * N.of_nat (variable_work p x + 1) * N.of_nat (function_width p + 1))%N.
  Proof. Admitted. (* PLAN-DEFECT: this interface supplies no cached graph bound. Counting
    nodes for the finite traversal costs the whole graph even when a variable is live only
    in one fixed return block; arbitrarily many disconnected empty blocks keep its region
    fixed. The driver computes this fuel once and its public clock is bounded separately. *)
  (** The driver prepares once, builds both indexes, searches each variable and groups
      rows. *)
  Lemma T2_rows : forall p,
    (T_live_in p <= R.T_prepare p +
      k_rows * N.of_nat (function_size p + live_size p + 1) *
        N.of_nat (function_width p + 1) + T_use_index (R.prepare p) +
      T_kill_index (R.prepare p) +
      fold_right N.add 0%N
        (map (T_explore (R.prepare p) (use_index (R.prepare p)) (kill_index (R.prepare p)))
          (U.universe (R.prepare p))))%N.
  Proof. Admitted. (* STUB *)

  (** Emitted rows name listed blocks and variables of the universe. *)
  Lemma live_in_ids : forall p row, In row (live_in p) ->
    In (fst row) (BC.nodes (R.prepare p)) /\ incl (snd row) (U.universe (R.prepare p)).
  Proof.
    intros p row Hin. unfold live_in in Hin. apply in_map_iff in Hin.
    destruct Hin as [b [<- Hb]]. split; [exact Hb|]. cbn.
    apply group_variables_values.
  Qed.
End LiveT.
