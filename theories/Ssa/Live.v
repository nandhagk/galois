(** * Indexed liveness producer

    Reverse graph searches collect live variables at the entry point of each block.
    For example, a use propagates to predecessors until an edge defines its variable.

    Main results
    - [live_driver_complexity] The liveness driver takes time linear in the function size plus
      the live-set size, times the variable width.

    Builds on: LiveSig and positive tries. *)

From Stdlib Require Import List PeanoNat PArith NArith Bool Lia.
From Argent Require Import Time Tactics Std Complexity.
From Galois.Base Require Import KeySig Key Trie.
From Galois.Graph Require Import DigraphSig.
From Galois.Program Require Import CfgSig VarsSig SsaSig.
From Galois.Ssa Require Import Lang LiveSig.
Import ComplexityNotations.
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
Definition live_seed_spec {A} (encode : A -> positive) (n : A) (x : positive)
    (table : ptrie (ptrie unit * list A)) : ptrie (ptrie unit * list A) :=
  let row := match trie_get x table with Some old => old | None => (Empty, []) end in
  if live_member (encode n) (fst row) then table else
    PTrieCode.set x (PTrieCode.set (encode n) tt (fst row), n :: snd row) table.

Definition live_seed {A} (encode : A -> positive) (n : A) (x : positive)
    (table : ptrie (ptrie unit * list A)) : ptrie (ptrie unit * list A) :=
  let row := match trie_get x table with Some old => old | None => (Empty, []) end in
  let c := encode n in
  if live_member c (fst row) then table else
    PTrieCode.set x (PTrieCode.set c tt (fst row), n :: snd row) table.
TimeFun live_seed.

(** Sharing a seed encoding preserves its membership row. *)
Lemma live_seed_agrees : forall A encode n x (table : ptrie (ptrie unit * list A)),
  live_seed encode n x table = live_seed_spec encode n x table.
Proof.
  reflexivity.
Qed.

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

Definition live_discover_spec {A} (encode : A -> positive) (n : A) (st : live_state A)
    : live_state A :=
  if live_member (encode n) (live_seen st) then st else
    {| live_seen := PTrieCode.set (encode n) tt (live_seen st);
       live_todo := n :: live_todo st;
       live_done := n :: live_done st |}.

Definition live_discover_code {A} (c : positive) (n : A) (st : live_state A)
    : live_state A :=
  if live_member c (live_seen st) then st else
    {| live_seen := PTrieCode.set c tt (live_seen st);
       live_todo := n :: live_todo st; live_done := n :: live_done st |}.
TimeFun live_discover_code.

Definition live_discover {A} (encode : A -> positive) (n : A) (st : live_state A)
    : live_state A :=
  live_discover_code (encode n) n st.
TimeFun live_discover.

(** Discovery with one shared encoding preserves the original worklist state. *)
Lemma live_discover_agrees : forall A encode n (st : live_state A),
  live_discover encode n st = live_discover_spec encode n st.
Proof.
  reflexivity.
Qed.

Definition live_initial {A} (encode : A -> positive) (seeds : list A) : live_state A :=
  fold_right (live_discover encode)
    {| live_seen := Empty; live_todo := []; live_done := [] |} seeds.
TimeFun live_initial.

Lemma live_lookup_correct : forall A key (table : ptrie A),
  live_lookup key table = trie_get key table.
Proof.
  intros A key; induction key as [key IH|key IH|]; intro table.
  - rewrite trie_get_xI. destruct table as [|n].
    + cbn [live_lookup trie_right]. symmetry. apply trie_get_empty.
    + cbn [live_lookup]. apply IH.
  - rewrite trie_get_xO. destruct table as [|n].
    + cbn [live_lookup trie_left]. symmetry. apply trie_get_empty.
    + cbn [live_lookup]. apply IH.
  - rewrite trie_get_xH. destruct table; reflexivity.
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
  unfold live_discover, live_discover_code. destruct (live_member (encode n) (live_seen st)) eqn:Hn.
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
  intros A encode st n [_ [Hseen _]] m. unfold live_discover, live_discover_code.
  destruct (live_member (encode n) (live_seen st)) eqn:Hn; cbn.
  - apply Hseen in Hn. split; [now right|intros [->|Hin]; assumption].
  - split; intros [Heq|Hin]; [left; symmetry|now right|left; symmetry|now right]; assumption.
Qed.

Lemma live_discover_todo : forall A (encode : A -> positive) st n,
  live_valid encode st -> forall m,
  In m (live_todo (live_discover encode n st)) <->
    (m = n /\ ~ In n (live_done st)) \/ In m (live_todo st).
Proof.
  intros A encode st n [_ [Hseen _]] m. unfold live_discover, live_discover_code.
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
  intros A encode st n. unfold live_discover, live_discover_code.
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
  unfold live_discover, live_discover_code. destruct (live_member (encode n) (live_seen st)); cbn;
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

(** Trie heights and list sums bound the indexed preprocessing clocks. *)
Fixpoint live_height_ne {A} (tree : trie_ne A) : nat :=
  match tree with
  | N001 rgt => S (live_height_ne rgt)
  | N010 _ => 1
  | N011 _ rgt => S (live_height_ne rgt)
  | N100 lft => S (live_height_ne lft)
  | N101 lft rgt => S (Nat.max (live_height_ne lft) (live_height_ne rgt))
  | N110 lft _ => S (live_height_ne lft)
  | N111 lft _ rgt => S (Nat.max (live_height_ne lft) (live_height_ne rgt))
  end.

Definition live_height {A} (tree : ptrie A) : nat :=
  match tree with Empty => 0 | Nodes nodes => live_height_ne nodes end.

Lemma live_height_witness : forall A (tree : trie_ne A),
  exists key value, trie_get key (Nodes tree) = Some value /\
    Pos.size_nat key = live_height_ne tree.
Proof.
  intros A tree; induction tree as [rgt IH|value|value rgt IH|lft IH|
    lft IHl rgt IHr|lft IH value|lft IHl value rgt IHr].
  - destruct IH as [key [value [Hget Hsize]]]. exists (xI key), value; cbn; auto.
  - exists xH, value; now split.
  - destruct IH as [key [other [Hget Hsize]]]. exists (xI key), other; cbn; auto.
  - destruct IH as [key [value [Hget Hsize]]]. exists (xO key), value; cbn; auto.
  - destruct (Nat.le_ge_cases (live_height_ne lft) (live_height_ne rgt)) as [Hle|Hge].
    + destruct IHr as [key [value [Hget Hsize]]]. exists (xI key), value; cbn.
      rewrite Nat.max_r by exact Hle; auto.
    + destruct IHl as [key [value [Hget Hsize]]]. exists (xO key), value; cbn.
      rewrite Nat.max_l by exact Hge; auto.
  - destruct IH as [key [other [Hget Hsize]]]. exists (xO key), other; cbn; auto.
  - destruct (Nat.le_ge_cases (live_height_ne lft) (live_height_ne rgt)) as [Hle|Hge].
    + destruct IHr as [key [other [Hget Hsize]]]. exists (xI key), other; cbn.
      rewrite Nat.max_r by exact Hle; auto.
    + destruct IHl as [key [other [Hget Hsize]]]. exists (xO key), other; cbn.
      rewrite Nat.max_l by exact Hge; auto.
Qed.

Lemma live_height_bound : forall A (tree : ptrie A) width,
  (forall key value, trie_get key tree = Some value -> Pos.size_nat key <= width) ->
  live_height tree <= width.
Proof.
  intros A [|tree] width Hwidth; [cbn; lia|].
  destruct (live_height_witness A tree) as [key [value [Hget Hsize]]].
  cbn [live_height]. rewrite <- Hsize. now apply Hwidth with value.
Qed.

Lemma live_height_left : forall A (tree : trie_ne A),
  live_height (trie_left (Nodes tree)) < live_height_ne tree.
Proof.
  intros A tree; destruct tree as [r|v|v r|l|l r|l v|l v r];
    cbn [trie_left live_height live_height_ne]; try lia.
  all: pose proof (Nat.le_max_l (live_height_ne l) (live_height_ne r)) as Hmax; lia.
Qed.

Lemma live_height_right : forall A (tree : trie_ne A),
  live_height (trie_right (Nodes tree)) < live_height_ne tree.
Proof.
  intros A tree; destruct tree as [r|v|v r|l|l r|l v|l v r];
    cbn [trie_right live_height live_height_ne]; try lia.
  all: pose proof (Nat.le_max_r (live_height_ne l) (live_height_ne r)) as Hmax; lia.
Qed.

Lemma T_live_lookup_bound : forall A key (tree : ptrie A),
  (T_live_lookup key tree <= 16 * N.of_nat (live_height tree + 1))%N.
Proof.
  intros A key; induction key as [key IH|key IH|]; intros [|tree];
    time_unfold @T_live_lookup; try (cbn [live_height]; lia).
  - specialize (IH (trie_right (Nodes tree))).
    pose proof (live_height_right A tree) as Hheight.
    assert (Hright : (T_trie_right (Nodes tree) <= 2)%N).
    { time_unfold @T_trie_right; destruct tree; lia. }
    cbn [live_height].
    rewrite Nat2N.inj_add in IH. nia.
  - specialize (IH (trie_left (Nodes tree))).
    pose proof (live_height_left A tree) as Hheight.
    assert (Hleft : (T_trie_left (Nodes tree) <= 2)%N).
    { time_unfold @T_trie_left; destruct tree; lia. }
    cbn [live_height].
    rewrite Nat2N.inj_add in IH. nia.
  - time_unfold @T_trie_value; destruct tree; cbn [live_height live_height_ne]; lia.
Qed.

Lemma T_live_member_bound : forall key tree,
  (T_live_member key tree <= 4 * N.of_nat (Pos.size_nat key + 1))%N.
Proof.
  intros key tree. time_unfold T_live_member.
  pose proof (PTrieT.T_trie_get_le unit key tree).
  destruct (trie_get key tree); rewrite Nat2N.inj_add; nia.
Qed.

Lemma live_seed_nodes : forall A encode n x (table : ptrie (ptrie unit * list A)),
  PTrie.nodes (live_seed encode n x table) <= PTrie.nodes table + Pos.size_nat x.
Proof.
  intros A encode n x table. unfold live_seed.
  destruct (trie_get x table) as [[seen row]|]; cbn [fst snd].
  - destruct (live_member (encode n) seen); [lia|apply PTrie.nodes_set].
  - destruct (live_member (encode n) Empty); [lia|apply PTrie.nodes_set].
Qed.

Lemma live_fold_clock_sum : forall A B (f : A -> B -> B) Tf cost xs base,
  (forall item, In item xs -> forall acc, (Tf item acc <= cost item)%N) ->
  (List.T_fold_right f Tf base xs <=
    fold_right (fun item n => cost item + 1 + n)%N 0%N xs + 1)%N.
Proof.
  intros A B f Tf cost xs; induction xs as [|item rest IH]; intros base Hbound.
  - time_step.
  - pose proof (Hbound item (or_introl eq_refl) (fold_right f base rest)) as Hhead.
    specialize (IH base ltac:(intros other Hin acc; apply Hbound; now right)).
    time_unfold @List.T_fold_right. cbn [fold_right]. nia.
Qed.

Lemma live_fold_clock_uniform : forall A B (f : A -> B -> B) Tf xs bound base,
  (forall item, In item xs -> forall acc, (Tf item acc <= bound)%N) ->
  (List.T_fold_right f Tf base xs <= (bound + 1) * N.of_nat (length xs) + 1)%N.
Proof.
  intros A B f Tf xs; induction xs as [|item rest IH]; intros bound base Hbound.
  - time_step.
  - pose proof (Hbound item (or_introl eq_refl) (fold_right f base rest)) as Hhead.
    specialize (IH bound base ltac:(intros other Hin acc; apply Hbound; now right)).
    time_step.
Qed.

Lemma live_map_clock_sum : forall A B (f : A -> B) Tf cost xs,
  (forall item, In item xs -> (Tf item <= cost item)%N) ->
  (ListDef.T_map f Tf xs <= fold_right (fun item n => cost item + 1 + n)%N 0%N xs + 1)%N.
Proof.
  intros A B f Tf cost xs; induction xs as [|item rest IH]; intro Hbound.
  - time_step.
  - pose proof (Hbound item (or_introl eq_refl)) as Hhead.
    specialize (IH ltac:(intros other Hin; apply Hbound; now right)).
    time_unfold @ListDef.T_map. cbn [fold_right]. nia.
Qed.

Lemma live_nat_sum_app : forall A (weight : A -> nat) xs ys,
  fold_right (fun x n => weight x + n) 0 (xs ++ ys) =
    fold_right (fun x n => weight x + n) 0 xs + fold_right (fun x n => weight x + n) 0 ys.
Proof.
  intros A weight xs; induction xs as [|x rest IH]; intro ys; cbn; [reflexivity|].
  rewrite IH; lia.
Qed.

Lemma live_weighted_incl : forall A (weight : A -> nat) xs ys, NoDup xs -> incl xs ys ->
  fold_right (fun x n => weight x + n) 0 xs <= fold_right (fun x n => weight x + n) 0 ys.
Proof.
  intros A weight xs ys Hdup; revert ys.
  induction Hdup as [|x rest Hfresh Hdup IH]; intros ys Hsub; [cbn; lia|].
  destruct (in_split x ys (Hsub x (or_introl eq_refl))) as [prefix [suffix ->]].
  assert (Hrest : incl rest (prefix ++ suffix)).
  { intros y Hin. specialize (Hsub y (or_intror Hin)).
    rewrite in_app_iff in Hsub. apply in_app_iff. destruct Hsub as [Hp|[Heq|Hs]];
      [now left|subst y; contradiction|now right]. }
  specialize (IH _ Hrest). rewrite live_nat_sum_app in IH.
  cbn [fold_right]. rewrite live_nat_sum_app. cbn [fold_right]. lia.
Qed.

Lemma live_pair_row_nodup : forall A (xs : list A) (x : positive),
  NoDup xs -> NoDup (map (fun n => (n, x)) xs).
Proof.
  intros A xs x Hdup; induction Hdup as [|n rest Hfresh Hdup IH]; cbn; [constructor|].
  constructor; [|exact IH]. intro Hin. apply in_map_iff in Hin.
  destruct Hin as [m [Heq Hm]]. injection Heq as ->. now apply Hfresh.
Qed.

Lemma live_fold_clock_weight : forall A B (f : A -> B -> B) Tf weight xs price base,
  (forall item, In item xs -> 1 <= weight item) ->
  (forall item, In item xs -> forall acc, (Tf item acc <= price * N.of_nat (weight item))%N) ->
  (List.T_fold_right f Tf base xs <=
    (price + 1) * N.of_nat (fold_right (fun item n => (weight item + n)%nat) 0%nat xs) + 1)%N.
Proof.
  intros A B f Tf weight xs; induction xs as [|item rest IH]; intros price base Hweight Hbound.
  - time_step.
  - pose proof (Hbound item (or_introl eq_refl) (fold_right f base rest)) as Hhead.
    pose proof (Hweight item (or_introl eq_refl)) as Hpositive.
    specialize (IH price base ltac:(intros other Hin; apply Hweight; now right)
      ltac:(intros other Hin acc; apply Hbound; now right)).
    time_unfold @List.T_fold_right. cbn [fold_right]. rewrite Nat2N.inj_add. nia.
Qed.

Lemma live_map_clock_uniform : forall A B (f : A -> B) Tf xs price,
  (forall item, In item xs -> (Tf item <= price)%N) ->
  (ListDef.T_map f Tf xs <= (price + 1) * N.of_nat (length xs) + 1)%N.
Proof.
  intros A B f Tf xs; induction xs as [|item rest IH]; intros price Hbound.
  - time_step.
  - pose proof (Hbound item (or_introl eq_refl)) as Hhead.
    specialize (IH price ltac:(intros other Hin; apply Hbound; now right)). time_step.
Qed.

Lemma live_fold_lengths : forall A B (values : A -> list B) items,
  fold_right (fun item n => length (values item) + 1 + n) 0 items =
    length items + length (flat_map values items).
Proof.
  intros A B values items; induction items as [|item rest IH]; [reflexivity|].
  change (length (values item) + 1 +
    fold_right (fun item n => length (values item) + 1 + n) 0 rest =
    S (length rest) + length (values item ++ flat_map values rest)).
  rewrite IH, length_app. lia.
Qed.

Lemma live_flat_map_length_mono : forall A B C (f : A -> list B) (g : A -> list C) items,
  (forall item, In item items -> length (f item) <= length (g item)) ->
  length (flat_map f items) <= length (flat_map g items).
Proof.
  intros A B C f g items; induction items as [|item rest IH]; intro Hbound; [reflexivity|].
  cbn [flat_map]. rewrite !length_app.
  pose proof (Hbound item (or_introl eq_refl)) as Hhead.
  specialize (IH ltac:(intros other Hin; apply Hbound; now right)). lia.
Qed.

Lemma live_seed_list_nodes : forall A encode n xs (table : ptrie (ptrie unit * list A)),
  PTrie.nodes (fold_right (live_seed encode n) table xs) <=
    PTrie.nodes table + fold_right (fun x amount => Pos.size_nat x + amount) 0 xs.
Proof.
  intros A encode n xs; induction xs as [|x rest IH]; intro table; cbn [fold_right]; [lia|].
  pose proof (live_seed_nodes A encode n x (fold_right (live_seed encode n) table rest))
    as Hhead. specialize (IH table). lia.
Qed.

Lemma live_seed_batch_nodes : forall A B encode (point : B -> A) values items table,
  PTrie.nodes (live_seed_batch encode point values items table) <= PTrie.nodes table +
    fold_right (fun x amount => Pos.size_nat x + amount) 0 (flat_map values items).
Proof.
  intros A B encode point values items; induction items as [|item rest IH]; intro table.
  - cbn [live_seed_batch fold_right flat_map]; lia.
  - cbn [live_seed_batch fold_right flat_map].
    fold (live_seed_batch encode point values rest table).
    pose proof (live_seed_list_nodes A encode (point item) (values item)
      (live_seed_batch encode point values rest table)) as Hhead.
    specialize (IH table). rewrite live_nat_sum_app. lia.
Qed.

Lemma live_bits_mass : forall xs width,
  (forall x, In x xs -> Pos.size_nat x <= width) ->
  fold_right (fun x amount => Pos.size_nat x + amount) 0 xs <= width * length xs.
Proof.
  intro xs; induction xs as [|x rest IH]; intros width Hwidth; cbn; [lia|].
  pose proof (Hwidth x (or_introl eq_refl)) as Hhead.
  specialize (IH width ltac:(intros y Hin; apply Hwidth; now right)). lia.
Qed.

Lemma live_sum_weight : forall A (cost : A -> N) (weight : A -> nat) xs price,
  (forall item, In item xs -> (cost item <= price * N.of_nat (weight item))%N) ->
  (fold_right N.add 0%N (map cost xs) <=
    price * N.of_nat (fold_right (fun item n => (weight item + n)%nat) 0%nat xs))%N.
Proof.
  intros A cost weight xs; induction xs as [|item rest IH]; intros price Hbound; cbn; [lia|].
  pose proof (Hbound item (or_introl eq_refl)) as Hhead.
  specialize (IH price ltac:(intros other Hin; apply Hbound; now right)).
  rewrite Nat2N.inj_add. nia.
Qed.

Lemma live_sum_uniform : forall A (cost : A -> N) xs price,
  (forall item, In item xs -> (cost item <= price)%N) ->
  (fold_right N.add 0%N (map cost xs) <= price * N.of_nat (length xs))%N.
Proof.
  intros A cost xs; induction xs as [|item rest IH]; intros price Hbound; cbn; [lia|].
  pose proof (Hbound item (or_introl eq_refl)) as Hhead.
  specialize (IH price ltac:(intros other Hin; apply Hbound; now right)). nia.
Qed.

Lemma live_sum_pair : forall A (f g : A -> N) xs,
  fold_right N.add 0%N (map (fun item => f item + g item)%N xs) =
    (fold_right N.add 0%N (map f xs) + fold_right N.add 0%N (map g xs))%N.
Proof.
  intros A f g xs; induction xs as [|item rest IH]; cbn; [reflexivity|]. rewrite IH. lia.
Qed.

Lemma live_sum_extra : forall A (weight : A -> nat) xs,
  fold_right (fun item n => weight item + 1 + n) 0 xs =
    fold_right (fun item n => weight item + n) 0 xs + length xs.
Proof.
  intros A weight xs; induction xs as [|item rest IH]; cbn; [reflexivity|]. rewrite IH. lia.
Qed.

(** An incoming edge stores its predecessor code and its own definition set. *)
Record live_edge (A : Type) := LiveEdge {
  live_pred : A;
  live_pred_code : positive;
  live_defs : ptrie unit
}.
Arguments LiveEdge {A}.
Arguments live_pred {A}.
Arguments live_pred_code {A}.
Arguments live_defs {A}.
TimeFun live_pred.
TimeFun live_pred_code.
TimeFun live_defs.

Module LiveCode (O : OPS)
    (P : TYPE with Definition t := func positive O.K O.G)
    (Q : TYPE) (R : LANG_PREPARE_OPS O Q)
    (BE : TYPE) (E N : KEY_OPS)
    (BC : CFG_INDEXED_OPS Q PosKeyCode BE) (C : CFG_INDEXED_OPS Q N E)
    (U : VARS_OPS Q N E C PosKeyCode)
    (SP : SSA_POINTS_OPS Q PosKeyCode BE BC N E C PosKeyCode U)
    <: LIVE_OPS O P Q R BE E N BC C U SP.

  Definition incoming_edge (q : Q.t) (e : E.t) : live_edge N.t :=
    let pred := C.src q e in
    LiveEdge pred (N.encode pred) (live_intersection (U.defs q e) None).

  (** Incidence rows may repeat edges. Deduplicating the edge inventory bounds setup
      by the graph load and each cached row by its public incidence length. *)
  Definition incoming_edges (q : Q.t) : list E.t :=
    live_done (live_initial E.encode (C.edges q)).

  Definition incoming_insert (q : Q.t) (e : E.t)
      (table : ptrie (list (live_edge N.t))) : ptrie (list (live_edge N.t)) :=
    let code := N.encode (C.dst q e) in
    PTrieCode.set code (incoming_edge q e :: index_row table code) table.

  Definition incoming_build (q : Q.t) (es : list E.t) : ptrie (list (live_edge N.t)) :=
    fold_right (incoming_insert q) Empty es.

  Definition incoming_table (q : Q.t) : ptrie (list (live_edge N.t)) :=
    incoming_build q (incoming_edges q).

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

  Definition add_predecessors_spec (q : Q.t) (kills : ptrie (ptrie (ptrie unit)))
      (x : positive) (n : N.t) (es : list E.t) (st : live_state N.t) : live_state N.t :=
    fold_right (fun e acc =>
      let pred := C.src q e in
      if live_killed kills (N.encode pred) (N.encode n) x then acc else
        live_discover N.encode pred acc) st es.

  Definition add_predecessors (q : Q.t) (kills : ptrie (ptrie (ptrie unit)))
      (x : positive) (n : N.t) (es : list E.t) (st : live_state N.t) : live_state N.t :=
    let cn := N.encode n in
    fold_right (fun e acc =>
      let pred := C.src q e in
      let cp := N.encode pred in
      if live_killed kills cp cn x then acc else
        live_discover_code cp pred acc) st es.

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

  (** Each parallel edge retains its own definitions, so any non-killing edge
      can discover the shared predecessor. *)
  Definition cached_step (x : positive) (le : live_edge N.t) (st : live_state N.t)
      : live_state N.t :=
    if live_member x (live_defs le) then st else
      live_discover_code (live_pred_code le) (live_pred le) st.

  Definition cached_predecessors (table : ptrie (list (live_edge N.t))) (x : positive)
      (n : N.t) (st : live_state N.t) : live_state N.t :=
    fold_right (cached_step x) st (index_row table (N.encode n)).

  Fixpoint cached_fuel (fuel : nat) (table : ptrie (list (live_edge N.t)))
      (x : positive) (st : live_state N.t) : live_state N.t :=
    match fuel with
    | 0 => st
    | S rest =>
      match live_todo st with
      | [] => st
      | n :: pending =>
        cached_fuel rest table x
          (cached_predecessors table x n
            {| live_seen := live_seen st; live_todo := pending; live_done := live_done st |})
      end
    end.

  Definition cached_search (fuel : nat) (seeds : ptrie (list N.t))
      (table : ptrie (list (live_edge N.t))) (x : positive) : list N.t :=
    live_done (cached_fuel fuel table x (live_initial N.encode (index_row seeds x))).

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

  (** Cache only listed points, whose encodings have the public width bound. *)
  Definition entry_block (q : Q.t) (listed : ptrie positive) (n : N.t)
      : option positive :=
    match live_lookup (SP.block_of_point q n) listed with
    | None => None
    | Some b =>
      if N.eqb n (C.src q (SP.parameter_edge q b)) then Some b else None
    end.

  Definition entry_insert (q : Q.t) (listed : ptrie positive) (n : N.t)
      (table : ptrie positive) : ptrie positive :=
    match entry_block q listed n with
    | Some b => PTrieCode.set (N.encode n) b table
    | None => table
    end.

  Definition entry_table (q : Q.t) (bs : list positive) : ptrie positive :=
    let listed := block_index bs in
    fold_right (entry_insert q listed) Empty (C.nodes q).

  Definition group_entry (table : ptrie positive) (x : positive) (n : N.t)
      (rows : ptrie (list positive)) : ptrie (list positive) :=
    match trie_get (N.encode n) table with
    | Some b => PTrieCode.set b (x :: index_row rows b) rows
    | None => rows
    end.

  Definition live_in_spec (p : P.t) : list (positive * list positive) :=
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

  Definition live_in_entries (p : P.t) : list (positive * list positive) :=
    let q := R.prepare p in
    let fuel := length (C.nodes q) in
    let seeds := seed_index q in
    let kills := reverse_kills q in
    let bs := BC.nodes q in
    let entries := entry_table q bs in
    let rows := fold_right (fun x acc =>
      fold_right (group_entry entries x) acc (search fuel q seeds kills x))
      Empty (U.universe q) in
    map (fun b => (b, index_row rows b)) bs.

  Definition live_in (p : P.t) : list (positive * list positive) :=
    let q := R.prepare p in
    let fuel := length (C.nodes q) in
    let seeds := seed_index q in
    let incoming := incoming_table q in
    let bs := BC.nodes q in
    let entries := entry_table q bs in
    let rows := fold_right (fun x acc =>
      fold_right (group_entry entries x) acc (cached_search fuel seeds incoming x))
      Empty (U.universe q) in
    map (fun b => (b, index_row rows b)) bs.
End LiveCode.

Module Live (O : OPS)
    (P : TYPE with Definition t := func positive O.K O.G)
    (Q : TYPE) (R : LANG_PREPARE_OPS O Q)
    (BE : TYPE) (E N : KEY)
    (BC : CFG Q PosKey BE) (C : CFG Q N E) (U : VARS Q N E C PosKey)
    (SP : SSA_POINTS Q PosKey BE BC N E C PosKey U)
    <: LIVE O P Q R BE E N BC C U SP.
  Include LiveCode O P Q R BE E N BC C U SP.

  (** Hoisting point encodings preserves predecessor discovery exactly. *)
  Lemma add_predecessors_agrees : forall q kills x n es st,
    add_predecessors q kills x n es st = add_predecessors_spec q kills x n es st.
  Proof.
    reflexivity.
  Qed.

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

  (** Cached predecessor identities retain their original source point. *)
  Lemma incoming_edge_pred : forall q e,
    live_pred (incoming_edge q e) = C.src q e.
  Proof.
    intros q e; reflexivity.
  Qed.

  (** Each cached code encodes the predecessor stored beside it. *)
  Lemma incoming_edge_code : forall q e,
    live_pred_code (incoming_edge q e) = N.encode (live_pred (incoming_edge q e)).
  Proof.
    intros q e; reflexivity.
  Qed.

  (** The cached definitions belong to this edge, including among parallel edges. *)
  Lemma incoming_edge_defs : forall q e x,
    live_member x (live_defs (incoming_edge q e)) = true <-> In x (U.defs q e).
  Proof.
    intros q e x. unfold incoming_edge; cbn [live_defs].
    rewrite live_intersection_spec. tauto.
  Qed.

  (** Edge deduplication keeps precisely the listed edge identities. *)
  Lemma incoming_edges_spec : forall q e,
    In e (incoming_edges q) <-> In e (C.edges q).
  Proof.
    intros q e. unfold incoming_edges. apply live_initial_done. exact E.encode_inj.
  Qed.

  (** Each edge identity enters the cache at most once. *)
  Lemma incoming_edges_nodup : forall q, NoDup (incoming_edges q).
  Proof.
    intro q. exact (proj1 (live_initial_valid E.t E.encode E.encode_inj (C.edges q))).
  Qed.

  (** Building a destination row filters its source edge list without changing its order. *)
  Lemma incoming_build_row : forall q es n,
    index_row (incoming_build q es) (N.encode n) =
      map (incoming_edge q) (filter (fun e => N.eqb (C.dst q e) n) es).
  Proof.
    intros q es; induction es as [|e rest IH]; intro n.
    - unfold incoming_build, index_row. cbn [fold_right].
      rewrite PTrie.get_empty. reflexivity.
    - cbn [incoming_build fold_right filter]. fold (incoming_build q rest).
      unfold incoming_insert. destruct (N.eqb_spec (C.dst q e) n) as [Heq|Hneq].
      + rewrite Heq, live_index_set_same. cbn [map]. now rewrite IH.
      + rewrite live_index_set_other.
        * apply IH.
        * intro Hcode. apply Hneq. symmetry. now apply N.encode_inj.
  Qed.

  (** Every cached row represents each incoming edge identity exactly once. *)
  Lemma incoming_table_spec : forall q n, C.wf q ->
    exists es, NoDup es /\
      (forall e, In e es <-> In e (C.inc q n)) /\
      index_row (incoming_table q) (N.encode n) = map (incoming_edge q) es.
  Proof.
    intros q n Hwf.
    exists (filter (fun e => N.eqb (C.dst q e) n) (incoming_edges q)).
    split; [apply NoDup_filter, incoming_edges_nodup|]. split.
    - intro e. rewrite filter_In, incoming_edges_spec, C.inc_spec by exact Hwf.
      destruct (N.eqb_spec (C.dst q e) n); intuition congruence.
    - unfold incoming_table. apply incoming_build_row.
  Qed.

  (** The cache returns only records constructed from incoming edges, and returns all of them. *)
  Lemma incoming_table_member : forall q n le, C.wf q ->
    (In le (index_row (incoming_table q) (N.encode n)) <->
      exists e, In e (C.inc q n) /\ le = incoming_edge q e).
  Proof.
    intros q n le Hwf.
    destruct (incoming_table_spec q n Hwf) as [es [Hdup [Hedges Hrow]]].
    rewrite Hrow, in_map_iff. split.
    - intros [e [<- He]]. exists e. split; [now apply Hedges|reflexivity].
    - intros [e [He ->]]. exists e. split; [reflexivity|now apply Hedges].
  Qed.

  (** A cached row is no longer than the public incoming list, even if that list repeats edges. *)
  Lemma incoming_table_length : forall q n, C.wf q ->
    length (index_row (incoming_table q) (N.encode n)) <= length (C.inc q n).
  Proof.
    intros q n Hwf.
    destruct (incoming_table_spec q n Hwf) as [es [Hdup [Hedges Hrow]]].
    rewrite Hrow, length_map. apply NoDup_incl_length; [exact Hdup|].
    intros e He. now apply Hedges.
  Qed.

  (** Deduplication cannot increase the combined edge and definition-occurrence budget. *)
  Lemma incoming_edges_work : forall q,
    length (incoming_edges q) + length (flat_map (U.defs q) (incoming_edges q)) <=
      length (C.edges q) + length (flat_map (U.defs q) (C.edges q)).
  Proof.
    intro q.
    pose proof (live_weighted_incl E.t (fun e => length (U.defs q e) + 1)
      (incoming_edges q) (C.edges q) (incoming_edges_nodup q)
      ltac:(intros e He; now apply incoming_edges_spec)) as Hwork.
    pose proof (live_fold_lengths E.t PosKey.t (U.defs q) (incoming_edges q)) as Hsource.
    pose proof (live_fold_lengths E.t PosKey.t (U.defs q) (C.edges q)) as Htarget.
    cbn beta in Hwork.
    rewrite Hsource, Htarget in Hwork.
    exact Hwork.
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
      + fold (live_discover N.encode (C.src q e)
          (add_predecessors q kills x n rest st)).
        rewrite live_discover_done by (now apply add_predecessors_valid).
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
      unfold live_discover_code in Hdone, Htodo.
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
    fold (live_discover N.encode (C.src q e) (add_predecessors q kills x n rest st)).
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

  (** Every cached row carries codes matching its stored predecessor points. *)
  Lemma incoming_table_codes : forall q n, C.wf q -> forall le,
    In le (index_row (incoming_table q) (N.encode n)) ->
    live_pred_code le = N.encode (live_pred le).
  Proof.
    intros q n Hwf le Hin. apply (incoming_table_member q n le Hwf) in Hin.
    destruct Hin as [e [He ->]]. apply incoming_edge_code.
  Qed.

  (** Grouped edge discovery preserves the worklist invariant when its stored codes agree. *)
  Lemma cached_rows_valid : forall x les st,
    (forall le, In le les -> live_pred_code le = N.encode (live_pred le)) ->
    live_valid N.encode st -> live_valid N.encode (fold_right (cached_step x) st les).
  Proof.
    intros x les; induction les as [|le rest IH]; intros st Hcodes Hvalid;
      cbn [fold_right]; [exact Hvalid|].
    unfold cached_step. destruct (live_member x (live_defs le)).
    - apply IH; [intros item Hin; apply Hcodes; now right|exact Hvalid].
    - rewrite (Hcodes le (or_introl eq_refl)).
      apply live_discover_valid; [exact N.encode_inj|].
      apply IH; [intros item Hin; apply Hcodes; now right|exact Hvalid].
  Qed.

  (** A cached predecessor step preserves distinct discovered and pending points. *)
  Lemma cached_predecessors_valid : forall q x n st, C.wf q ->
    live_valid N.encode st ->
    live_valid N.encode (cached_predecessors (incoming_table q) x n st).
  Proof.
    intros q x n st Hwf Hvalid. unfold cached_predecessors.
    apply cached_rows_valid; [now apply incoming_table_codes|exact Hvalid].
  Qed.

  (** Adding one live predecessor preserves semantic soundness. *)
  Lemma live_discover_sound : forall q x n st,
    In n (C.nodes q) ->
    point_live (C.nodes q) (C.out q) (C.dst q) (U.uses q) (U.defs q) (U.exits q) x n ->
    live_sound q x st -> live_sound q x (live_discover N.encode n st).
  Proof.
    intros q x n st Hnode Hlive Hsound. unfold live_discover, live_discover_code.
    destruct (live_member (N.encode n) (live_seen st)); [exact Hsound|].
    intros m [<-|Hin]; [now split|now apply Hsound].
  Qed.

  (** Cached edges propagate only across an edge that does not define the variable. *)
  Lemma cached_rows_sound : forall q x n les st, C.wf q ->
    incl les (index_row (incoming_table q) (N.encode n)) ->
    point_live (C.nodes q) (C.out q) (C.dst q) (U.uses q) (U.defs q) (U.exits q) x n ->
    live_sound q x st -> live_sound q x (fold_right (cached_step x) st les).
  Proof.
    intros q x n les; induction les as [|le rest IH]; intros st Hwf Hrows Hlive Hsound;
      cbn [fold_right]; [exact Hsound|].
    assert (Htail : live_sound q x (fold_right (cached_step x) st rest)).
    { apply IH; [exact Hwf|intros item Hin; apply Hrows; now right|exact Hlive|exact Hsound]. }
    destruct (proj1 (incoming_table_member q n le Hwf) (Hrows le (or_introl eq_refl)))
      as [e [He ->]].
    unfold cached_step. destruct (live_member x (live_defs (incoming_edge q e))) eqn:Hclear;
      [exact Htail|].
    rewrite incoming_edge_code, incoming_edge_pred. apply live_discover_sound; [| |exact Htail].
    - exact (proj1 (C.edges_nodes q e Hwf (proj1 (proj1 (C.inc_spec q n e Hwf) He)))).
    - apply (C.inc_spec q n e Hwf) in He. destruct He as [He Hdst].
      apply Point_live_next with e.
      + apply C.out_spec; [exact Hwf|now split].
      + intro Hdef. apply (proj2 (incoming_edge_defs q e x)) in Hdef. congruence.
      + exact (proj2 (C.edges_nodes q e Hwf He)).
      + now rewrite Hdst.
  Qed.

  (** A cached expansion preserves the live region after popping its current point. *)
  Lemma cached_step_sound : forall q x st n pending, C.wf q ->
    live_valid N.encode st -> live_sound q x st -> live_todo st = n :: pending ->
    live_sound q x (cached_predecessors (incoming_table q) x n
      {| live_seen := live_seen st; live_todo := pending; live_done := live_done st |}).
  Proof.
    intros q x st n pending Hwf Hvalid Hsound Htodo. unfold cached_predecessors.
    apply cached_rows_sound with n; [exact Hwf|apply incl_refl| |exact Hsound].
    assert (Hdone : In n (live_done st)).
    { apply (proj2 (proj2 (proj2 Hvalid))). rewrite Htodo; now left. }
    exact (proj2 (Hsound n Hdone)).
  Qed.

  (** The cached search preserves its worklist invariant for every amount of fuel. *)
  Lemma cached_fuel_valid : forall fuel q x st, C.wf q ->
    live_valid N.encode st ->
    live_valid N.encode (cached_fuel fuel (incoming_table q) x st).
  Proof.
    induction fuel as [|fuel IH]; intros q x st Hwf Hvalid; cbn [cached_fuel];
      [exact Hvalid|].
    destruct (live_todo st) as [|n pending] eqn:Htodo; [exact Hvalid|].
    apply IH; [exact Hwf|]. apply cached_predecessors_valid; [exact Hwf|].
    eapply live_pop_valid; eassumption.
  Qed.

  (** Every discovered cached-search point is semantically live. *)
  Lemma cached_fuel_sound : forall fuel q x st, C.wf q ->
    live_valid N.encode st -> live_sound q x st ->
    live_sound q x (cached_fuel fuel (incoming_table q) x st).
  Proof.
    induction fuel as [|fuel IH]; intros q x st Hwf Hvalid Hsound;
      cbn [cached_fuel]; [exact Hsound|].
    destruct (live_todo st) as [|n pending] eqn:Htodo; [exact Hsound|].
    apply IH; [exact Hwf| |].
    - apply cached_predecessors_valid; [exact Hwf|]. eapply live_pop_valid; eassumption.
    - eapply cached_step_sound; eassumption.
  Qed.

  (** Cached search returns each point at most once. *)
  Lemma cached_search_nodup : forall q x, C.wf q ->
    NoDup (cached_search (length (C.nodes q)) (seed_index q) (incoming_table q) x).
  Proof.
    intros q x Hwf. unfold cached_search.
    apply (proj1 (cached_fuel_valid (length (C.nodes q)) q x
      (live_initial N.encode (index_row (seed_index q) x)) Hwf
      (live_initial_valid N.t N.encode N.encode_inj _))).
  Qed.

  (** Cached search stays within the original semantic live-point region. *)
  Lemma cached_search_live : forall q x n, C.wf q ->
    In n (cached_search (length (C.nodes q)) (seed_index q) (incoming_table q) x) ->
    In n (C.nodes q) /\
      point_live (C.nodes q) (C.out q) (C.dst q) (U.uses q) (U.defs q) (U.exits q) x n.
  Proof.
    intros q x n Hwf Hin.
    eapply (cached_fuel_sound (length (C.nodes q)) q x
      (live_initial N.encode (index_row (seed_index q) x)) Hwf); [| |exact Hin].
    - apply live_initial_valid; exact N.encode_inj.
    - intros m Hm. apply live_initial_done in Hm; [|exact N.encode_inj].
      destruct (seed_index_live q x m Hwf Hm) as [Hnode [_ Hlive]]; now split.
  Qed.

  (** A cached row adds exactly the predecessors of edges that do not kill the variable. *)
  Lemma cached_rows_done : forall x les st,
    (forall le, In le les -> live_pred_code le = N.encode (live_pred le)) ->
    live_valid N.encode st -> forall m,
    In m (live_done (fold_right (cached_step x) st les)) <->
      In m (live_done st) \/ exists le, In le les /\
        live_member x (live_defs le) = false /\ live_pred le = m.
  Proof.
    intros x les; induction les as [|le rest IH]; intros st Hcodes Hvalid m;
      cbn [fold_right].
    - split; [now left|intros [Hin|[item [Hin _]]]; [assumption|contradiction]].
    - assert (Htailcodes : forall item, In item rest ->
        live_pred_code item = N.encode (live_pred item)).
      { intros item Hin; apply Hcodes; now right. }
      unfold cached_step at 1.
      destruct (live_member x (live_defs le)) eqn:Hkill.
      + rewrite IH by assumption. split.
        * intros [Hin|[item [Hi Hrest]]]; [now left|].
          right; exists item; split; [now right|exact Hrest].
        * intros [Hin|[item [[->|Hi] [Hclear Hpred]]]]; [now left|congruence|].
          right; exists item; auto.
      + rewrite (Hcodes le (or_introl eq_refl)).
        fold (live_discover N.encode (live_pred le) (fold_right (cached_step x) st rest)).
        rewrite live_discover_done by (now apply cached_rows_valid).
        rewrite IH by assumption. split.
        * intros [Heq|[Hin|[item [Hi Hrest]]]].
          -- right; exists le; split; [now left|split; [exact Hkill|now symmetry]].
          -- now left.
          -- right; exists item; split; [now right|exact Hrest].
        * intros [Hin|[item [[->|Hi] [Hclear Hpred]]]].
          -- now right; left.
          -- left; now symmetry.
          -- right; right; exists item; auto.
  Qed.

  (** Reading a cached predecessor row implements the incoming edge relation exactly. *)
  Lemma cached_predecessors_done : forall q x n st, C.wf q ->
    live_valid N.encode st -> forall m,
    In m (live_done (cached_predecessors (incoming_table q) x n st)) <->
      In m (live_done st) \/ exists e, In e (C.inc q n) /\
        ~ In x (U.defs q e) /\ C.src q e = m.
  Proof.
    intros q x n st Hwf Hvalid m. unfold cached_predecessors.
    rewrite cached_rows_done by (first [now apply incoming_table_codes|exact Hvalid]).
    split.
    - intros [Hin|[le [Hle [Hclear Hpred]]]]; [now left|].
      apply (incoming_table_member q n le Hwf) in Hle.
      destruct Hle as [e [He ->]]. right; exists e. split; [exact He|]. split.
      + intro Hdef. apply (proj2 (incoming_edge_defs q e x)) in Hdef. congruence.
      + exact Hpred.
    - intros [Hin|[e [He [Hnot Hsrc]]]]; [now left|].
      right; exists (incoming_edge q e). split.
      + apply (incoming_table_member q n (incoming_edge q e) Hwf). exists e; auto.
      + split; [|exact Hsrc].
        destruct (live_member x (live_defs (incoming_edge q e))) eqn:Hkill; [|reflexivity].
        exfalso. apply Hnot, (proj1 (incoming_edge_defs q e x)), Hkill.
  Qed.

  (** Any point processed after additions was already processed before them. *)
  Lemma cached_rows_processed : forall x les st m,
    In m (live_done (fold_right (cached_step x) st les)) ->
    ~ In m (live_todo (fold_right (cached_step x) st les)) ->
    In m (live_done st) /\ ~ In m (live_todo st).
  Proof.
    intros x les; induction les as [|le rest IH]; intros st m Hdone Htodo;
      [now split|].
    cbn [fold_right] in Hdone, Htodo.
    set (tail := fold_right (cached_step x) st rest) in Hdone, Htodo.
    unfold cached_step in Hdone, Htodo.
    destruct (live_member x (live_defs le)); [now apply IH with (m := m)|].
    unfold live_discover_code in Hdone, Htodo.
    destruct (live_member (live_pred_code le)
      (live_seen tail)).
    - now apply IH with (m := m).
    - cbn in Hdone, Htodo. apply IH with (m := m); tauto.
  Qed.

  (** A new discovery increases the pending and discovered counts together. *)
  Lemma cached_rows_balance : forall x les st,
    length (live_done (fold_right (cached_step x) st les)) + length (live_todo st) =
      length (live_done st) + length (live_todo (fold_right (cached_step x) st les)).
  Proof.
    intros x les; induction les as [|le rest IH]; intro st; cbn [fold_right]; [lia|].
    set (tail := fold_right (cached_step x) st rest).
    unfold cached_step. destruct (live_member x (live_defs le)); [apply IH|].
    unfold live_discover_code.
    destruct (live_member (live_pred_code le)
      (live_seen tail)); [apply IH|].
    change (S (length (live_done tail)) + length (live_todo st) =
      length (live_done st) + S (length (live_todo tail))).
    specialize (IH st). fold tail in IH. lia.
  Qed.

  (** All already processed points have propagated across their non-killing incoming edges. *)
  Definition cached_ready (q : Q.t) (x : positive) (st : live_state N.t) : Prop :=
    forall n, In n (live_done st) -> ~ In n (live_todo st) -> forall e,
      In e (C.inc q n) -> ~ In x (U.defs q e) -> In (C.src q e) (live_done st).

  (** Processing one cached predecessor row preserves closure of all processed points. *)
  Lemma cached_step_ready : forall q x st n pending, C.wf q ->
    live_valid N.encode st -> cached_ready q x st -> live_todo st = n :: pending ->
    cached_ready q x (cached_predecessors (incoming_table q) x n
      {| live_seen := live_seen st; live_todo := pending; live_done := live_done st |}).
  Proof.
    intros q x st n pending Hwf Hvalid Hready Htodo m Hdone Hnot e He Hclear.
    assert (Hpop := live_pop_valid st n pending Hvalid Htodo).
    unfold cached_predecessors in Hdone, Hnot.
    destruct (cached_rows_processed x _ _ m Hdone Hnot) as [Hold Hpending].
    cbn in Hold, Hpending.
    apply cached_predecessors_done; [exact Hwf|exact Hpop|].
    destruct (node_eq_dec m n) as [->|Hneq].
    - right; exists e; auto.
    - left. apply Hready with m; try assumption. rewrite Htodo; cbn. intuition congruence.
  Qed.

  (** The node-count fuel suffices because a point is popped at most once. *)
  Lemma cached_fuel_correct : forall fuel q x st, C.wf q ->
    live_valid N.encode st -> live_sound q x st -> cached_ready q x st ->
    length (C.nodes q) + length (live_todo st) <= length (live_done st) + fuel ->
    let result := cached_fuel fuel (incoming_table q) x st in
    live_valid N.encode result /\ live_sound q x result /\
      cached_ready q x result /\ live_todo result = [] /\
      incl (live_done st) (live_done result).
  Proof.
    induction fuel as [|fuel IH]; intros q x st Hwf Hvalid Hsound Hready Hbudget.
    - cbn [cached_fuel]. assert (Hlength : length (live_done st) <= length (C.nodes q)).
      { apply NoDup_incl_length; [exact (proj1 Hvalid)|].
        intros n Hin; exact (proj1 (Hsound n Hin)). }
      assert (Hempty : live_todo st = []) by (apply length_zero_iff_nil; lia).
      split; [exact Hvalid|]. split; [exact Hsound|]. split; [exact Hready|].
      split; [exact Hempty|apply incl_refl].
    - cbn [cached_fuel]. destruct (live_todo st) as [|n pending] eqn:Htodo.
      + split; [exact Hvalid|]. split; [exact Hsound|]. split; [exact Hready|].
        split; [exact Htodo|apply incl_refl].
      + set (popped := {| live_seen := live_seen st; live_todo := pending;
                         live_done := live_done st |}).
        set (next := cached_predecessors (incoming_table q) x n popped).
        assert (Hpop : live_valid N.encode popped) by (eapply live_pop_valid; eassumption).
        assert (Hnext : live_valid N.encode next) by (now apply cached_predecessors_valid).
        assert (Hnext_sound : live_sound q x next) by (eapply cached_step_sound; eassumption).
        assert (Hnext_ready : cached_ready q x next) by (eapply cached_step_ready; eassumption).
        assert (Hnext_budget : length (C.nodes q) + length (live_todo next) <=
          length (live_done next) + fuel).
        { pose proof (cached_rows_balance x
            (index_row (incoming_table q) (N.encode n)) popped) as Hbalance.
          change (length (live_done next) + length (live_todo popped) =
            length (live_done popped) + length (live_todo next)) in Hbalance.
          unfold popped in Hbalance; cbn in Hbalance. cbn in Hbudget. lia. }
        destruct (IH q x next Hwf Hnext Hnext_sound Hnext_ready Hnext_budget)
          as [Hv [Hs [Hr [Ht Hsub]]]].
        split; [exact Hv|]. split; [exact Hs|]. split; [exact Hr|]. split; [exact Ht|].
        intros m Hin. apply Hsub. apply cached_predecessors_done;
          [exact Hwf|exact Hpop|now left].
  Qed.

  (** Cached search returns every live point exactly once, including across parallel edges. *)
  Lemma cached_search_spec : forall q x, C.wf q ->
    NoDup (cached_search (length (C.nodes q)) (seed_index q) (incoming_table q) x) /\ forall n,
      In n (cached_search (length (C.nodes q)) (seed_index q) (incoming_table q) x) <->
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
    assert (Hready : cached_ready q x initial).
    { intros n Hin Hnot. exfalso. apply Hnot.
      unfold initial. rewrite live_initial_todo. exact Hin. }
    assert (Hbudget : length (C.nodes q) + length (live_todo initial) <=
      length (live_done initial) + length (C.nodes q)).
    { unfold initial. rewrite live_initial_todo. lia. }
    destruct (cached_fuel_correct (length (C.nodes q)) q x initial Hwf Hvalid Hsound Hready
      Hbudget) as [Hresult [Hlive [Hclosed [Hempty Hcontains]]]].
    split; [exact (proj1 Hresult)|]. intro n. split; [apply Hlive|].
    intros [Hnode Hn]; revert Hnode.
    induction Hn as [n Hexit|n e Hout Huse|n e Hout Hnot Hdst Hn IH]; intro Hnode.
    - apply Hcontains. apply live_initial_done; [exact N.encode_inj|].
      apply seed_index_spec. now left.
    - apply Hcontains. apply live_initial_done; [exact N.encode_inj|].
      apply seed_index_spec. right; exists e. apply C.out_spec in Hout; [|exact Hwf]. tauto.
    - apply C.out_spec in Hout; [|exact Hwf]. destruct Hout as [He Hsrc].
      rewrite <- Hsrc. apply Hclosed with (C.dst q e); [now apply IH| | |exact Hnot].
      + rewrite Hempty. tauto.
      + apply C.inc_spec; auto.
  Qed.

  (** The cached and reference searches enumerate the same live points. *)
  Lemma cached_search_membership : forall q x n, C.wf q ->
    (In n (cached_search (length (C.nodes q)) (seed_index q) (incoming_table q) x) <->
      In n (search (length (C.nodes q)) q (seed_index q) (reverse_kills q) x)).
  Proof.
    intros q x n Hwf. rewrite (proj2 (cached_search_spec q x Hwf) n).
    symmetry. exact (proj2 (search_spec q x Hwf) n).
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

  (** An entry lookup adds only the variable being grouped. *)
  Lemma group_entry_values : forall table x n rows allowed,
    In x allowed -> (forall b, incl (index_row rows b) allowed) ->
    forall b, incl (index_row (group_entry table x n rows) b) allowed.
  Proof.
    intros table x n rows allowed Hx Hrows b. unfold group_entry.
    destruct (trie_get (N.encode n) table) as [target|]; [|apply Hrows].
    destruct (Pos.eq_dec b target) as [->|Hneq].
    - rewrite live_index_set_same. intros y [->|Hin]; [exact Hx|now apply (Hrows target)].
    - rewrite live_index_set_other by exact Hneq. apply Hrows.
  Qed.

  (** Grouping a point list preserves the allowed variable set. *)
  Lemma group_entries_values : forall table x ns rows allowed,
    In x allowed -> (forall b, incl (index_row rows b) allowed) ->
    forall b, incl (index_row (fold_right (group_entry table x) rows ns) b) allowed.
  Proof.
    intros table x ns; induction ns as [|n rest IH]; intros rows allowed Hx Hrows b;
      cbn; [apply Hrows|]. apply group_entry_values; [exact Hx|now apply IH].
  Qed.

  (** One grouping step adds at most one row entry. *)
  Lemma group_entry_mass : forall table x n rows bs, NoDup bs ->
    live_rows_mass bs (group_entry table x n rows) <= live_rows_mass bs rows + 1.
  Proof.
    intros table x n rows bs Hdup. unfold group_entry.
    destruct (trie_get (N.encode n) table) as [target|]; [|lia].
    now apply live_rows_mass_add.
  Qed.

  (** Grouping a point list adds at most one row entry per point. *)
  Lemma group_entries_mass : forall table x ns rows bs, NoDup bs ->
    live_rows_mass bs (fold_right (group_entry table x) rows ns) <=
      live_rows_mass bs rows + length ns.
  Proof.
    intros table x ns; induction ns as [|n rest IH]; intros rows bs Hdup; cbn; [lia|].
    pose proof (group_entry_mass table x n
      (fold_right (group_entry table x) rows rest) bs Hdup).
    specialize (IH rows bs Hdup). lia.
  Qed.

  (** The complete grouping fold emits only enumerated variables. *)
  Lemma group_entry_variables_values : forall table xs visits,
    forall b, incl (index_row (fold_right (fun x acc =>
      fold_right (group_entry table x) acc (visits x)) Empty xs) b) xs.
  Proof.
    intros table xs visits; induction xs as [|x rest IH]; intro b; cbn.
    - unfold index_row; rewrite PTrie.get_empty. intros y Hin; contradiction.
    - apply group_entries_values; [now left|].
      intros target y Hin; right; now apply (IH target).
  Qed.

  (** The complete grouping fold emits at most one entry per visited pair. *)
  Lemma group_entry_variables_mass : forall table xs visits bs, NoDup bs ->
    live_rows_mass bs (fold_right (fun x acc =>
      fold_right (group_entry table x) acc (visits x)) Empty xs) <=
      length (flat_map (fun x => map (fun n => (n, x)) (visits x)) xs).
  Proof.
    intros table xs visits bs Hdup; induction xs as [|x rest IH]; cbn.
    - rewrite live_rows_mass_empty. lia.
    - rewrite length_app, length_map.
      pose proof (group_entries_mass table x (visits x)
        (fold_right (fun y acc => fold_right (group_entry table y) acc (visits y))
          Empty rest) bs Hdup). lia.
  Qed.

  (** Every cached block comes from the same entry test at a listed point. *)
  Lemma entry_nodes_binding : forall q listed ns key b,
    trie_get key (fold_right (entry_insert q listed) Empty ns) = Some b ->
    exists n, In n ns /\ key = N.encode n /\ entry_block q listed n = Some b.
  Proof.
    intros q listed ns; induction ns as [|n rest IH]; intros key b Hget.
    - cbn [fold_right] in Hget. rewrite PTrie.get_empty in Hget. discriminate.
    - cbn [fold_right] in Hget. unfold entry_insert in Hget.
      destruct (entry_block q listed n) as [target|] eqn:Hentry.
      + destruct (Pos.eq_dec key (N.encode n)) as [->|Hneq].
        * rewrite PTrie.get_set_same in Hget. injection Hget as <-.
          exists n. split; [now left|]. now split.
        * rewrite PTrie.get_set_other in Hget by exact Hneq.
          destruct (IH key b Hget) as [m [Hm [Hkey Hb]]].
          exists m. split; [now right|]. now split.
      + destruct (IH key b Hget) as [m [Hm [Hkey Hb]]].
        exists m. split; [now right|]. now split.
  Qed.

  (** A cache lookup returns the original entry decision at every listed point. *)
  Lemma entry_nodes_agrees : forall q listed ns n, In n ns ->
    trie_get (N.encode n) (fold_right (entry_insert q listed) Empty ns) =
      entry_block q listed n.
  Proof.
    intros q listed ns; induction ns as [|m rest IH]; intros n Hin; [contradiction|].
    cbn [fold_right]. unfold entry_insert at 1.
    destruct (entry_block q listed m) as [b|] eqn:Hentry.
    - destruct (Pos.eq_dec (N.encode n) (N.encode m)) as [Heq|Hneq].
      + apply N.encode_inj in Heq. subst n. rewrite PTrie.get_set_same. symmetry; exact Hentry.
      + rewrite PTrie.get_set_other by exact Hneq. apply IH.
        destruct Hin as [<-|Hin]; [contradiction|exact Hin].
    - destruct Hin as [<-|Hin]; [|now apply IH]. rewrite Hentry.
      destruct (trie_get (N.encode m) (fold_right (entry_insert q listed) Empty rest))
        as [b|] eqn:Hget; [|reflexivity].
      destruct (entry_nodes_binding q listed rest (N.encode m) b Hget)
        as [n [Hn [Hcode Hb]]].
      apply N.encode_inj in Hcode. subst n. rewrite Hentry in Hb. discriminate.
  Qed.

  (** Replacing an entry test by its cache preserves a grouping step. *)
  Lemma group_entry_agrees : forall q bs x n rows, In n (C.nodes q) ->
    group_entry (entry_table q bs) x n rows = group_point q (block_index bs) x n rows.
  Proof.
    intros q bs x n rows Hn. unfold group_entry, entry_table.
    rewrite entry_nodes_agrees by exact Hn. unfold entry_block, group_point.
    destruct (live_lookup (SP.block_of_point q n) (block_index bs)) as [b|];
      [destruct (N.eqb n (C.src q (SP.parameter_edge q b)))|]; reflexivity.
  Qed.

  (** Caching preserves a grouping fold over listed points. *)
  Lemma group_entries_agrees : forall q bs x ns rows, incl ns (C.nodes q) ->
    fold_right (group_entry (entry_table q bs) x) rows ns =
      fold_right (group_point q (block_index bs) x) rows ns.
  Proof.
    intros q bs x ns; induction ns as [|n rest IH]; intros rows Hnodes; [reflexivity|].
    cbn [fold_right]. rewrite IH by (intros m Hm; apply Hnodes; now right).
    apply group_entry_agrees, Hnodes. now left.
  Qed.

  (** The cache preserves row order and contents whenever the point graph is well formed. *)
  Lemma live_in_entries_agrees : forall p, C.wf (R.prepare p) -> live_in_entries p = live_in_spec p.
  Proof.
    intros p Hwf. unfold live_in_entries, live_in_spec.
    set (q := R.prepare p) in *.
    set (bs := BC.nodes q).
    set (visits := search (length (C.nodes q)) q (seed_index q) (reverse_kills q)).
    assert (Hfold : forall xs rows,
      fold_right (fun x acc => fold_right (group_entry (entry_table q bs) x)
        acc (visits x)) rows xs =
      fold_right (fun x acc => fold_right (group_point q (block_index bs) x)
        acc (visits x)) rows xs).
    { intro xs; induction xs as [|x rest IH]; intro rows; [reflexivity|].
      cbn [fold_right]. rewrite IH. apply group_entries_agrees.
      intros n Hn. exact (proj1 (proj1 (proj2 (search_spec q x Hwf) n) Hn)). }
    now rewrite Hfold.
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

  TimeFun incoming_edge.
  TimeFun incoming_edges.
  TimeFun incoming_insert.
  TimeFun incoming_build.
  TimeFun incoming_table.

  TimeFun add_predecessors.
  TimeFun explore_fuel.
  TimeFun search.

  TimeFun cached_step.
  TimeFun cached_predecessors.
  TimeFun cached_fuel.
  TimeFun cached_search.

  TimeFun block_index.
  TimeFun group_point.
  TimeFun entry_block.
  TimeFun entry_insert.
  TimeFun entry_table.
  TimeFun group_entry.
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
  (** The cached producer enumerates only pairs of the original charged live region. *)
  Definition cached_region (p : P.t) : list (N.t * positive) :=
    let q := R.prepare p in
    flat_map (fun x => map (fun n => (n, x))
      (cached_search (length (C.nodes q)) (seed_index q) (incoming_table q) x))
      (U.universe q).

  Lemma cached_region_nodup : forall p, NoDup (cached_region p).
  Proof.
    intro p. unfold cached_region. apply live_pairs_nodup; [apply U.universe_nodup|].
    intro x. apply cached_search_nodup. exact (proj2 (PB.prepared_wf p)).
  Qed.

  Lemma cached_region_incl : forall p, incl (cached_region p) (live_region p).
  Proof.
    intros p [n x] Hin. unfold cached_region in Hin. apply live_pairs_in in Hin.
    destruct Hin as [Hx Hn]. apply (proj2 (live_region_spec p) n x).
    destruct (cached_search_live (R.prepare p) x n (proj2 (PB.prepared_wf p)) Hn)
      as [Hnode Hlive]. repeat split; assumption.
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
    set (visits := cached_search (length (C.nodes q)) (seed_index q) (incoming_table q)).
    set (rows := fold_right (fun x acc =>
      fold_right (group_entry (entry_table q bs) x) acc (visits x)) Empty (U.universe q)).
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
    { assert (Hcache : live_rows_mass bs rows <= length (cached_region p)).
      { apply group_entry_variables_mass. apply BC.nodes_nodup.
        exact (proj1 (PB.prepared_wf p)). }
      eapply Nat.le_trans; [exact Hcache|].
      apply NoDup_incl_length; [apply cached_region_nodup|apply cached_region_incl]. }
    assert (Hregion : length (live_region p) <= live_size p).
    { unfold live_size. apply live_weighted_length. }
    pose proof (PB.block_nodes_le p) as Hblocks. unfold bs, q in *. lia.
  Qed.
  (** Dependency constants and syntax widths give a common primitive cost budget. *)
  Definition live_clock_scale : N :=
    (PTrieT.c_trie + N.c_key + E.c_key + C.c_cfg + C.c_cfg_adj + BC.c_cfg_adj +
      U.c_vars + SP.c_points + R.c_prepare + PB.c_present + 1)%N.
  Definition live_clock_width (p : P.t) := N.of_nat (function_width p + 1).
  Definition live_clock_atom (p : P.t) :=
    (64 * live_clock_scale * live_clock_scale * live_clock_width p)%N.

  Lemma live_clock_scale_positive : (1 <= live_clock_scale)%N.
  Proof.
    unfold live_clock_scale; lia.
  Qed.

  Lemma live_clock_width_positive : forall p, (1 <= live_clock_width p)%N.
  Proof.
    intro p; unfold live_clock_width; rewrite Nat2N.inj_add; lia.
  Qed.

  Lemma live_clock_scale_le_atom : forall p, (live_clock_scale <= live_clock_atom p)%N.
  Proof.
    intro p. pose proof live_clock_scale_positive as Hscale.
    pose proof (live_clock_width_positive p) as Hwidth. unfold live_clock_atom; nia.
  Qed.

  Lemma live_clock_atom_positive : forall p, (1 <= live_clock_atom p)%N.
  Proof.
    intro p. pose proof live_clock_scale_positive as Hscale.
    pose proof (live_clock_scale_le_atom p) as Hbound. lia.
  Qed.

  Lemma live_clock_product : forall p c units,
    (c <= live_clock_scale -> units <= live_clock_scale * live_clock_width p ->
      c * units <= live_clock_atom p)%N.
  Proof.
    intros p c units Hc Hu. pose proof live_clock_scale_positive as Hscale.
    unfold live_clock_atom. nia.
  Qed.

  Lemma live_clock_units : forall p units,
    (units <= live_clock_scale * live_clock_width p -> 16 * units <= live_clock_atom p)%N.
  Proof.
    intros p units Hu. pose proof live_clock_scale_positive as Hscale.
    unfold live_clock_atom. nia.
  Qed.

  Lemma live_occurrences_spec : forall q x,
    In x (U.occurrences q) <-> In x (U.universe q).
  Proof.
    intros q x. unfold U.occurrences. rewrite in_app_iff, U.universe_spec.
    split.
    - intros [Hin|Hin]; apply in_flat_map in Hin; destruct Hin as [item [Hi Hx]].
      + left; exists item; split; [exact Hi|now apply in_app_iff in Hx].
      + right; exists item; now split.
    - intros [[e [He Hx]]|[n [Hn Hx]]].
      + left; apply in_flat_map; exists e; split; [exact He|now apply in_app_iff].
      + right; apply in_flat_map; exists n; now split.
  Qed.

  Lemma live_universe_length : forall q, length (U.universe q) <= length (U.occurrences q).
  Proof.
    intro q. apply NoDup_incl_length; [apply U.universe_nodup|].
    intros x Hin. now apply live_occurrences_spec.
  Qed.

  Lemma live_variable_width : forall p x, In x (U.universe (R.prepare p)) ->
    Pos.size_nat x <= function_width p.
  Proof.
    intros p x Hin. apply live_occurrences_spec in Hin.
    pose proof (PB.occurrence_width_le p) as Hwidth.
    assert (Hmax : forall xs y, In y xs -> Pos.size_nat y <=
      fold_right Nat.max 0 (map Pos.size_nat xs)).
    { intros xs; induction xs as [|y rest IH]; intros z Hz; [contradiction|].
      cbn. destruct Hz as [->|Hz].
      - apply Nat.le_max_l.
      - eapply Nat.le_trans; [now apply IH|apply Nat.le_max_r]. }
    pose proof (Hmax (U.occurrences (R.prepare p)) x Hin) as Hx.
    unfold U.occurrence_width in Hwidth. change
      (fold_right Nat.max 0 (map Pos.size_nat (U.occurrences (R.prepare p))) <= function_width p)
      in Hwidth. lia.
  Qed.

  Lemma live_node_key : forall p n, In n (C.nodes (R.prepare p)) ->
    (N.of_nat (N.bits n + 1) <= live_clock_scale * live_clock_width p)%N.
  Proof.
    intros p n Hin. pose proof (PB.point_bits_le p n Hin) as Hbits.
    assert (Hscale : (PB.c_present + 1 <= live_clock_scale)%N)
      by (unfold live_clock_scale; lia).
    pose proof (live_clock_width_positive p) as Hwidth.
    fold (live_clock_width p) in Hbits. rewrite Nat2N.inj_add. nia.
  Qed.

  Lemma live_edge_key : forall p e, In e (C.edges (R.prepare p)) ->
    (N.of_nat (E.bits e + 1) <= live_clock_scale * live_clock_width p)%N.
  Proof.
    intros p e Hin. pose proof (PB.edge_bits_le p e Hin) as Hbits.
    assert (Hscale : (PB.c_present + 1 <= live_clock_scale)%N)
      by (unfold live_clock_scale; lia).
    pose proof (live_clock_width_positive p) as Hwidth.
    fold (live_clock_width p) in Hbits. rewrite Nat2N.inj_add. nia.
  Qed.

  Lemma live_variable_key : forall p x, In x (U.universe (R.prepare p)) ->
    (N.of_nat (Pos.size_nat x + 1) <= live_clock_scale * live_clock_width p)%N.
  Proof.
    intros p x Hin. pose proof (live_variable_width p x Hin) as Hx.
    pose proof live_clock_scale_positive as Hscale. unfold live_clock_width. nia.
  Qed.

  Lemma live_block_key : forall p b, In b (BC.nodes (R.prepare p)) ->
    (N.of_nat (Pos.size_nat b + 1) <= live_clock_scale * live_clock_width p)%N.
  Proof.
    intros p b Hin. pose proof (PB.block_bits_le p b (or_introl Hin)) as Hb.
    change (Pos.size_nat b <= function_width p) in Hb.
    pose proof live_clock_scale_positive as Hscale. unfold live_clock_width. nia.
  Qed.

  Lemma live_get_atom : forall A p key (table : ptrie A),
    (N.of_nat (Pos.size_nat key + 1) <= live_clock_scale * live_clock_width p ->
      T_trie_get key table <= live_clock_atom p)%N.
  Proof.
    intros A p key table Hkey. PTrieT.trie_get_le.
    pose proof (live_clock_units p _ Hkey) as Hbound. rewrite Nat2N.inj_add in Hbound. nia.
  Qed.

  Lemma live_set_atom : forall A p key (value : A) table,
    (N.of_nat (Pos.size_nat key + 1) <= live_clock_scale * live_clock_width p ->
      PTrieCode.T_set key value table <= live_clock_atom p)%N.
  Proof.
    intros A p key value table Hkey. eapply N.le_trans; [apply PTrieT.T_set_le|].
    apply live_clock_product; [unfold live_clock_scale; lia|exact Hkey].
  Qed.

  Lemma live_member_atom : forall p key table,
    (N.of_nat (Pos.size_nat key + 1) <= live_clock_scale * live_clock_width p ->
      T_live_member key table <= live_clock_atom p)%N.
  Proof.
    intros p key table Hkey. pose proof (T_live_member_bound key table) as Hmember.
    pose proof (live_clock_units p _ Hkey) as Hbound. lia.
  Qed.

  Lemma live_row_atom : forall A p (table : ptrie (list A)) key,
    (N.of_nat (Pos.size_nat key + 1) <= live_clock_scale * live_clock_width p ->
      T_index_row table key <= live_clock_atom p)%N.
  Proof.
    intros A p table key Hkey. time_unfold @T_index_row.
    PTrieT.trie_get_le. pose proof (live_clock_units p _ Hkey) as Hbound.
    rewrite Nat2N.inj_add in Hbound. destruct (trie_get key table); nia.
  Qed.

  Lemma live_encode_node_atom : forall p n, In n (C.nodes (R.prepare p)) ->
    (N.T_encode n <= live_clock_atom p)%N.
  Proof.
    intros p n Hin. eapply N.le_trans; [apply N.T_encode_le|].
    apply live_clock_product; [unfold live_clock_scale; lia|now apply live_node_key].
  Qed.

  Lemma live_encode_edge_atom : forall p e, In e (C.edges (R.prepare p)) ->
    (E.T_encode e <= live_clock_atom p)%N.
  Proof.
    intros p e Hin. eapply N.le_trans; [apply E.T_encode_le|].
    apply live_clock_product; [unfold live_clock_scale; lia|now apply live_edge_key].
  Qed.

  Lemma live_eqb_node_atom : forall p n other, In n (C.nodes (R.prepare p)) ->
    (N.T_eqb n other <= live_clock_atom p)%N.
  Proof.
    intros p n other Hin. eapply N.le_trans; [apply N.T_eqb_le|].
    apply live_clock_product; [unfold live_clock_scale; lia|now apply live_node_key].
  Qed.

  Lemma live_reader_atom : forall p c bits amount clock,
    (c <= live_clock_scale -> N.of_nat (bits + 1) <= live_clock_scale * live_clock_width p ->
      clock <= c * N.of_nat (bits + amount + 1) ->
      clock <= live_clock_atom p * N.of_nat (amount + 1))%N.
  Proof.
    intros p c bits amount clock Hc Hbits Hclock.
    pose proof (live_clock_product p c _ Hc Hbits) as Hbase.
    pose proof (live_clock_scale_le_atom p) as Hscale.
    replace (bits + amount + 1) with ((bits + 1) + amount) in Hclock by lia.
    rewrite Nat2N.inj_add in Hclock. rewrite Nat2N.inj_add. nia.
  Qed.

  Lemma live_uses_atom : forall p e, In e (C.edges (R.prepare p)) ->
    (U.T_uses (R.prepare p) e <=
      live_clock_atom p * N.of_nat (length (U.uses (R.prepare p) e) + 1))%N.
  Proof.
    intros p e Hin. eapply live_reader_atom with (c := U.c_vars) (bits := E.bits e);
      [unfold live_clock_scale; lia| |apply U.T_uses_le].
    now apply live_edge_key.
  Qed.

  Lemma live_defs_atom : forall p e, In e (C.edges (R.prepare p)) ->
    (U.T_defs (R.prepare p) e <=
      live_clock_atom p * N.of_nat (length (U.defs (R.prepare p) e) + 1))%N.
  Proof.
    intros p e Hin. eapply live_reader_atom with (c := U.c_vars) (bits := E.bits e);
      [unfold live_clock_scale; lia| |apply U.T_defs_le].
    now apply live_edge_key.
  Qed.

  Lemma live_exits_atom : forall p n, In n (C.nodes (R.prepare p)) ->
    (U.T_exits (R.prepare p) n <=
      live_clock_atom p * N.of_nat (length (U.exits (R.prepare p) n) + 1))%N.
  Proof.
    intros p n Hin. eapply live_reader_atom with (c := U.c_vars) (bits := N.bits n);
      [unfold live_clock_scale; lia| |apply U.T_exits_le].
    now apply live_node_key.
  Qed.

  Lemma live_inc_atom : forall p n, In n (C.nodes (R.prepare p)) ->
    (C.T_inc (R.prepare p) n <=
      live_clock_atom p * N.of_nat (length (C.inc (R.prepare p) n) + 1))%N.
  Proof.
    intros p n Hin. eapply live_reader_atom with (c := C.c_cfg_adj) (bits := N.bits n);
      [unfold live_clock_scale; lia| |apply C.T_inc_le].
    now apply live_node_key.
  Qed.

  Definition live_index_budget : N :=
    (65536 * live_clock_scale * live_clock_scale * live_clock_scale)%N.

  Definition live_driver_budget : N :=
    (1048576 * live_clock_scale * live_clock_scale * live_clock_scale * live_clock_scale)%N.

  Definition c_live : N := live_driver_budget.
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
  Definition k_index : N := live_index_budget.
  Definition k_rows : N := live_driver_budget.
  Definition visits p x := filter (fun pair => Pos.eqb (snd pair) x) (live_region p).
  Definition variable_work p x := fold_right (fun pair n =>
    1 + length (C.inc (R.prepare p) (fst pair)) + n) 0 (visits p x).
  Definition searched p x :=
    explore (R.prepare p) (use_index (R.prepare p)) (kill_index (R.prepare p)) x.
  (** Indexed use points of a variable are distinct charged live pairs. *)
  Lemma use_index_spec : forall p x,
    NoDup (index_row (use_index (R.prepare p)) x) /\
    forall n, In n (index_row (use_index (R.prepare p)) x) -> In (n, x) (live_region p).
  Proof.
    intros p x. split; [apply seed_index_nodup|]. intros n Hin.
    apply (proj2 (live_region_spec p) n x).
    apply seed_index_live; [exact (proj2 (PB.prepared_wf p))|exact Hin].
  Qed.
  (** The kill index answers, for a variable and a listed edge, whether the edge defines it. *)
  Lemma kill_index_spec : forall p x e, In e (C.edges (R.prepare p)) ->
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
    unfold live_discover, live_discover_code. destruct (live_member (N.encode (C.src q e))
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
  Lemma searched_nodup : forall p x, NoDup (searched p x).
  Proof.
    intros p x. pose proof (plan_fuel_valid (length (C.nodes (R.prepare p)))
      (R.prepare p) (kill_index (R.prepare p)) x
      (live_initial N.encode (index_row (use_index (R.prepare p)) x))
      (live_initial_valid N.t N.encode N.encode_inj _)) as Hvalid.
    exact (proj1 Hvalid).
  Qed.
  (** Every visited search point belongs to its charged semantic region. *)
  Lemma searched_region : forall p x n,
    In n (searched p x) -> In (n, x) (live_region p).
  Proof.
    intros p x n Hin. apply (proj2 (live_region_spec p) n x).
    assert (Hwf := proj2 (PB.prepared_wf p)).
    assert (Hsound : live_sound (R.prepare p) x
      (plan_fuel (length (C.nodes (R.prepare p))) (R.prepare p) (kill_index (R.prepare p)) x
        (live_initial N.encode (index_row (use_index (R.prepare p)) x)))).
    { apply plan_fuel_sound; [exact Hwf| | |].
      - intros e He. rewrite live_pair_member_spec. now apply kill_index_spec.
      - apply live_initial_valid; exact N.encode_inj.
      - intros m Hm. apply live_initial_done in Hm; [|exact N.encode_inj].
        destruct (seed_index_live (R.prepare p) x m Hwf Hm) as [Hn [_ Hl]]; now split. }
    destruct (Hsound n Hin) as [Hn Hl]. split; [exact Hn|]. split; [|exact Hl].
    now apply point_live_universe with n.
  Qed.
  (** Deduplicated variables partition the total live-incidence budget. *)
  Lemma live_size_partition : forall p,
    fold_right (fun x n => variable_work p x + n) 0 (U.universe (R.prepare p)) =
      live_size p.
  Proof.
    intro p. unfold variable_work, visits, live_size.
    apply live_weighted_partition; [apply U.universe_nodup|].
    intros [n x] Hin. apply (proj2 (live_region_spec p) n x) in Hin. tauto.
  Qed.
  (** Each index scans syntax occurrences and updates only bounded identifier paths. *)
  Definition live_graph_load (q : Q.t) : nat :=
    length (C.nodes q) + length (C.edges q) + length (U.occurrences q) + 1.

  Lemma live_graph_load_bound : forall p,
    (N.of_nat (live_graph_load (R.prepare p)) <=
      2 * live_clock_scale * N.of_nat (function_size p + 1))%N.
  Proof.
    intro p. pose proof (PB.points_le p) as Hpoints.
    assert (Hpresent : (PB.c_present + 1 <= live_clock_scale)%N)
      by (unfold live_clock_scale; lia).
    pose proof live_clock_scale_positive as Hscale.
    unfold live_graph_load. rewrite Nat2N.inj_add. nia.
  Qed.

  Lemma live_uses_universe : forall q e x, In e (C.edges q) -> In x (U.uses q e) ->
    In x (U.universe q).
  Proof.
    intros q e x He Hx. apply U.universe_spec. left; exists e; split; [exact He|now left].
  Qed.

  Lemma live_defs_universe : forall q e x, In e (C.edges q) -> In x (U.defs q e) ->
    In x (U.universe q).
  Proof.
    intros q e x He Hx. apply U.universe_spec. left; exists e; split; [exact He|now right].
  Qed.

  Lemma live_exits_universe : forall q n x, In n (C.nodes q) -> In x (U.exits q n) ->
    In x (U.universe q).
  Proof.
    intros q n x Hn Hx. apply U.universe_spec. right; exists n; now split.
  Qed.

  Lemma live_seed_count : forall q,
    length (flat_map (U.uses q) (C.edges q)) + length (flat_map (U.exits q) (C.nodes q)) <=
      length (U.occurrences q).
  Proof.
    intro q. unfold U.occurrences; rewrite length_app.
    assert (Hedges : length (flat_map (U.uses q) (C.edges q)) <=
      length (flat_map (fun e => U.uses q e ++ U.defs q e) (C.edges q))).
    { apply live_flat_map_length_mono; intros e Hin; rewrite length_app; lia. }
    lia.
  Qed.

  Lemma live_def_count : forall q,
    length (flat_map (U.defs q) (C.edges q)) <= length (U.occurrences q).
  Proof.
    intro q. unfold U.occurrences; rewrite length_app.
    assert (Hedges : length (flat_map (U.defs q) (C.edges q)) <=
      length (flat_map (fun e => U.uses q e ++ U.defs q e) (C.edges q))).
    { apply live_flat_map_length_mono; intros e Hin; rewrite length_app; lia. }
    lia.
  Qed.

  Lemma seed_table_nodes : forall p,
    PTrie.nodes (seed_table (R.prepare p)) <=
      function_width p * length (U.occurrences (R.prepare p)).
  Proof.
    intro p. set (q := R.prepare p).
    pose proof (live_seed_batch_nodes N.t N.t N.encode (fun n => n) (U.exits q) (C.nodes q)
      (live_seed_batch N.encode (C.src q) (U.uses q) (C.edges q) Empty)) as Hnodes.
    pose proof (live_seed_batch_nodes N.t E.t N.encode (C.src q) (U.uses q) (C.edges q) Empty)
      as Hedges.
    assert (Huses : fold_right (fun x n => Pos.size_nat x + n) 0
      (flat_map (U.uses q) (C.edges q)) <= function_width p *
      length (flat_map (U.uses q) (C.edges q))).
    { apply live_bits_mass; intros x Hin. apply in_flat_map in Hin.
      destruct Hin as [e [He Hx]]. apply live_variable_width; eapply live_uses_universe;
        eassumption. }
    assert (Hexits : fold_right (fun x n => Pos.size_nat x + n) 0
      (flat_map (U.exits q) (C.nodes q)) <= function_width p *
      length (flat_map (U.exits q) (C.nodes q))).
    { apply live_bits_mass; intros x Hin. apply in_flat_map in Hin.
      destruct Hin as [n [Hn Hx]]. apply live_variable_width; eapply live_exits_universe;
        eassumption. }
    pose proof (live_seed_count q) as Hcount.
    change (PTrie.nodes (seed_table q) <= function_width p * length (U.occurrences q)).
    fold (seed_table q) in Hnodes. change (PTrie.nodes (@Empty (ptrie unit * list N.t))) with 0
      in Hedges.
    eapply Nat.le_trans; [exact Hnodes|].
    eapply Nat.le_trans.
    - apply Nat.add_le_mono; [eapply Nat.le_trans; [exact Hedges|exact Huses]|exact Hexits].
    - rewrite <- Nat.mul_add_distr_l. apply Nat.mul_le_mono_l. exact Hcount.
  Qed.

  Lemma live_nodes_atom : forall p,
    (C.T_nodes (R.prepare p) <= live_clock_atom p * N.of_nat (length (C.nodes (R.prepare p)) +
      1))%N.
  Proof.
    intro p. pose proof (C.T_nodes_le (R.prepare p)) as Hnodes.
    assert (Hc : (C.c_cfg_adj <= live_clock_scale)%N) by (unfold live_clock_scale; lia).
    pose proof (live_clock_scale_le_atom p) as Hatom. nia.
  Qed.

  Lemma live_edges_atom : forall p,
    (C.T_edges (R.prepare p) <= live_clock_atom p * N.of_nat (length (C.edges (R.prepare p)) +
      1))%N.
  Proof.
    intro p. pose proof (C.T_edges_le (R.prepare p)) as Hedges.
    assert (Hc : (C.c_cfg <= live_clock_scale)%N) by (unfold live_clock_scale; lia).
    pose proof (live_clock_scale_le_atom p) as Hatom. nia.
  Qed.

  Lemma live_src_atom : forall p e, (C.T_src (R.prepare p) e <= live_clock_atom p)%N.
  Proof.
    intros p e. pose proof (C.T_src_le (R.prepare p) e) as Hsrc.
    assert (Hc : (C.c_cfg <= live_clock_scale)%N) by (unfold live_clock_scale; lia).
    pose proof (live_clock_scale_le_atom p) as Hatom. lia.
  Qed.

  Lemma live_dst_atom : forall p e, (C.T_dst (R.prepare p) e <= live_clock_atom p)%N.
  Proof.
    intros p e. pose proof (C.T_dst_le (R.prepare p) e) as Hdst.
    assert (Hc : (C.c_cfg <= live_clock_scale)%N) by (unfold live_clock_scale; lia).
    pose proof (live_clock_scale_le_atom p) as Hatom. lia.
  Qed.

  Lemma live_seed_atom : forall p n x table,
    In n (C.nodes (R.prepare p)) -> In x (U.universe (R.prepare p)) ->
    (T_live_seed N.encode N.T_encode n x table <= 16 * live_clock_atom p)%N.
  Proof.
    intros p n x table Hn Hx.
    pose proof (live_clock_atom_positive p) as Hpositive.
    pose proof (live_node_key p n Hn) as Hnode.
    pose proof (live_variable_key p x Hx) as Hvar.
    pose proof (live_encode_node_atom p n Hn) as Hencode.
    pose proof (live_get_atom _ p x table Hvar) as Hget.
    time_unfold @T_live_seed.
    destruct (trie_get x table) as [[seen row]|]; cbn [fst snd]; time_simpl.
    all: let n := constr:(n) in match goal with
      | |- context [T_live_member (N.encode n) ?seen] =>
        pose proof (live_member_atom p (N.encode n) seen Hnode) as Hmember;
        pose proof (live_set_atom _ p (N.encode n) tt seen Hnode) as Hsetnode;
        destruct (live_member (N.encode n) seen)
      end.
    all: try nia.
    all: let x := constr:(x) in let table := constr:(table) in match goal with
      | |- context [PTrieCode.T_set x ?value table] =>
        pose proof (live_set_atom _ p x value table Hvar) as Hsetvar
      end; nia.
  Qed.

  Lemma live_seed_batch_atom : forall p B (point : B -> N.t) T_point values T_values items table,
    (forall item, In item items -> (T_point item <= live_clock_atom p)%N) ->
    (forall item, In item items -> In (point item) (C.nodes (R.prepare p))) ->
    (forall item, In item items ->
      (T_values item <= live_clock_atom p * N.of_nat (length (values item) + 1))%N) ->
    (forall item, In item items -> incl (values item) (U.universe (R.prepare p))) ->
    (T_live_seed_batch N.encode N.T_encode point T_point values T_values items table <=
      32 * live_clock_atom p * N.of_nat (length items + length (flat_map values items) + 1))%N.
  Proof.
    intros p B point T_point values T_values items table Hpoint Hnode Hreader Hvars.
    pose proof (live_clock_atom_positive p) as Hpositive. time_unfold @T_live_seed_batch.
    let table := constr:(table) in let items := constr:(items) in match goal with
    | |- (1 + List.T_fold_right ?step ?clock table items <= _)%N =>
      assert (Hfold : (List.T_fold_right step clock table items <=
        (24 * live_clock_atom p + 1) *
          N.of_nat (fold_right (fun item n => (length (values item) + 1 + n)%nat) 0%nat items) +
            1)%N)
    end.
    { apply live_fold_clock_weight; [intros; lia|]. intros item Hin state; cbn beta.
      assert (Hinner : (List.T_fold_right (live_seed N.encode (point item))
        (fun x acc => T_live_seed N.encode N.T_encode (point item) x acc) state (values item) <=
        (16 * live_clock_atom p + 1) * N.of_nat (length (values item)) + 1)%N).
      { apply live_fold_clock_uniform; intros x Hx acc.
        apply live_seed_atom; [now apply Hnode|now apply (Hvars item Hin)]. }
      eapply N.le_trans with (m := (1 + (live_clock_atom p +
        live_clock_atom p * N.of_nat (length (values item) + 1) +
        ((16 * live_clock_atom p + 1) * N.of_nat (length (values item)) + 1)))%N).
      - apply N.add_le_mono_l. apply N.add_le_mono; [|exact Hinner].
        apply N.add_le_mono; [now apply Hpoint|now apply Hreader].
      - rewrite Nat2N.inj_add. nia. }
    rewrite live_fold_lengths in Hfold.
    eapply N.le_trans; [apply N.add_le_mono_l; exact Hfold|].
    rewrite Nat2N.inj_add. nia.
  Qed.

  Lemma seed_table_atom : forall p,
    (T_seed_table (R.prepare p) <=
      128 * live_clock_atom p * N.of_nat (live_graph_load (R.prepare p)))%N.
  Proof.
    intro p. set (q := R.prepare p). pose proof (proj2 (PB.prepared_wf p)) as Hwf.
    pose proof (live_clock_atom_positive p) as Hpositive.
    pose proof (live_nodes_atom p) as Hnodes. pose proof (live_edges_atom p) as Hedges.
    assert (Hedge_batch : (T_live_seed_batch N.encode N.T_encode (C.src q)
      (fun e => C.T_src q e) (U.uses q) (fun e => U.T_uses q e) (C.edges q) Empty <=
      32 * live_clock_atom p * N.of_nat
        (length (C.edges q) + length (flat_map (U.uses q) (C.edges q)) + 1))%N).
    { apply live_seed_batch_atom.
      - intros e He; apply live_src_atom.
      - intros e He; exact (proj1 (C.edges_nodes q e Hwf He)).
      - intros e He; now apply live_uses_atom.
      - intros e He x Hx; now apply live_uses_universe with e. }
    assert (Hnode_batch : (T_live_seed_batch N.encode N.T_encode (fun n => n) (fun _ => 1%N)
      (U.exits q) (fun n => U.T_exits q n) (C.nodes q)
      (live_seed_batch N.encode (C.src q) (U.uses q) (C.edges q) Empty) <=
      32 * live_clock_atom p * N.of_nat
        (length (C.nodes q) + length (flat_map (U.exits q) (C.nodes q)) + 1))%N).
    { apply live_seed_batch_atom.
      - intros n Hn; exact Hpositive.
      - intros n Hn; exact Hn.
      - intros n Hn; now apply live_exits_atom.
      - intros n Hn x Hx; now apply live_exits_universe with n. }
    pose proof (live_seed_count q) as Hcount.
    time_unfold T_seed_table.
    fold q in Hnodes, Hedges |- *.
    change (1 + (C.T_nodes q + (C.T_edges q +
      T_live_seed_batch N.encode N.T_encode (C.src q) (fun e => C.T_src q e)
        (U.uses q) (fun e => U.T_uses q e) (C.edges q) Empty) +
      T_live_seed_batch N.encode N.T_encode (fun n => n) (fun _ => 1%N)
        (U.exits q) (fun n => U.T_exits q n) (C.nodes q)
        (live_seed_batch N.encode (C.src q) (U.uses q) (C.edges q) Empty)) <=
      128 * live_clock_atom p * N.of_nat (live_graph_load q))%N.
    unfold live_graph_load. rewrite !Nat2N.inj_add in *. nia.
  Qed.

  Lemma seed_map_atom : forall p Tf,
    (forall row : ptrie unit * list N.t, (Tf row <= 1)%N) ->
    (PTrieT.T_map snd Tf (seed_table (R.prepare p)) <=
      live_clock_atom p * N.of_nat (length (U.occurrences (R.prepare p)) + 1))%N.
  Proof.
    intros p Tf Hf. pose proof (PTrieT.T_map_le _ _ (@snd (ptrie unit) (list N.t)) Tf
      (seed_table (R.prepare p)) 1%N Hf) as Hmap.
    change (PTrieT.nodes (seed_table (R.prepare p))) with
      (PTrie.nodes (seed_table (R.prepare p))) in Hmap.
    pose proof (seed_table_nodes p) as Hnodes.
    assert (HnodesN : (N.of_nat (PTrie.nodes (seed_table (R.prepare p))) <=
      N.of_nat (function_width p) * N.of_nat (length (U.occurrences (R.prepare p))))%N).
    { rewrite <- Nat2N.inj_mul. lia. }
    assert (Htrie : (PTrieT.c_trie <= live_clock_scale)%N) by (unfold live_clock_scale; lia).
    pose proof live_clock_scale_positive as Hscale.
    assert (Hheight : (N.of_nat (PTrie.nodes (seed_table (R.prepare p)) + 1) <=
      live_clock_width p * N.of_nat (length (U.occurrences (R.prepare p)) + 1))%N).
    { unfold live_clock_width. rewrite !Nat2N.inj_add. nia. }
    assert (Hcost : (PTrieT.c_trie * (1 + 1) * live_clock_width p <= live_clock_atom p)%N).
    { unfold live_clock_atom. apply N.mul_le_mono_r. nia. }
    eapply N.le_trans; [exact Hmap|].
    eapply N.le_trans.
    - apply N.mul_le_mono_l; exact Hheight.
    - rewrite N.mul_assoc. apply N.mul_le_mono_r. exact Hcost.
  Qed.

  Lemma seed_index_atom : forall p,
    (T_seed_index (R.prepare p) <=
      256 * live_clock_atom p * N.of_nat (live_graph_load (R.prepare p)))%N.
  Proof.
    intro p. pose proof (seed_table_atom p) as Htable.
    pose proof (seed_map_atom p (fun row => Datatypes.T_snd row)
      ltac:(intros; time_simpl; lia)) as Hmap.
    pose proof (live_clock_atom_positive p) as Hpositive.
    time_unfold T_seed_index. unfold live_graph_load in *.
    rewrite !Nat2N.inj_add in *. nia.
  Qed.

  Lemma use_index_atom : forall p,
    (T_use_index (R.prepare p) <=
      512 * live_clock_atom p * N.of_nat (live_graph_load (R.prepare p)))%N.
  Proof.
    intro p. pose proof (seed_index_atom p) as Hindex.
    pose proof (live_clock_atom_positive p) as Hpositive.
    time_unfold T_use_index. unfold live_graph_load in *.
    rewrite !Nat2N.inj_add in *. nia.
  Qed.

  Lemma live_pair_insert_atom : forall p x edge table,
    (N.of_nat (Pos.size_nat x + 1) <= live_clock_scale * live_clock_width p)%N ->
    (N.of_nat (Pos.size_nat edge + 1) <= live_clock_scale * live_clock_width p)%N ->
    (T_live_pair_insert x edge table <= 4 * live_clock_atom p)%N.
  Proof.
    intros p x edge table Hx Hedge.
    pose proof (live_clock_atom_positive p) as Hpositive.
    pose proof (live_get_atom _ p x table Hx) as Hget.
    time_unfold T_live_pair_insert.
    destruct (trie_get x table) as [row|].
    all: let edge := constr:(edge) in match goal with
      | |- context [PTrieCode.T_set edge tt ?row] =>
        pose proof (live_set_atom _ p edge tt row Hedge) as Hinner;
        pose proof (live_set_atom _ p x (PTrieCode.set edge tt row) table Hx) as Houter
      end; nia.
  Qed.

  Lemma kill_index_atom : forall p,
    (T_kill_index (R.prepare p) <=
      32 * live_clock_atom p * N.of_nat (live_graph_load (R.prepare p)))%N.
  Proof.
    intro p. set (q := R.prepare p).
    pose proof (live_clock_atom_positive p) as Hpositive.
    pose proof (live_edges_atom p) as Hedges.
    pose proof (live_def_count q) as Hdefs.
    time_unfold T_kill_index. fold q in Hedges |- *.
    let q := constr:(q) in match goal with
    | |- context [List.T_fold_right ?step ?clock Empty (C.edges q)] =>
      assert (Hfold : (List.T_fold_right step clock Empty (C.edges q) <=
        (16 * live_clock_atom p + 1) * N.of_nat
          (fold_right (fun e n => (length (U.defs q e) + 1 + n)%nat) 0%nat (C.edges q))
        + 1)%N)
    end.
    { apply live_fold_clock_weight; [intros; lia|]. intros e He state; cbn beta.
      pose proof (live_defs_atom p e He) as Hreader.
      pose proof (live_encode_edge_atom p e He) as Hencode.
      pose proof (live_edge_key p e He) as Hedge.
      let state := constr:(state) in let q := constr:(q) in let e := constr:(e) in
      match goal with
      | |- context [List.T_fold_right ?step ?clock state (U.defs q e)] =>
        assert (Hinner : (List.T_fold_right step clock state (U.defs q e) <=
          (8 * live_clock_atom p + 1) * N.of_nat (length (U.defs q e)) + 1)%N)
      end.
      { apply live_fold_clock_uniform; intros x Hx acc; cbn beta.
        pose proof (live_variable_key p x (live_defs_universe q e x He Hx)) as Hvar.
        pose proof (live_pair_insert_atom p x (E.encode e) acc Hvar Hedge) as Hinsert.
        unfold T_live_pair_insert in Hinsert.
        destruct (trie_get x acc); nia. }
      eapply N.le_trans with (m := (1 + (live_clock_atom p *
        N.of_nat (length (U.defs q e) + 1) +
        ((8 * live_clock_atom p + 1) * N.of_nat (length (U.defs q e)) + 1)))%N).
      - apply N.add_le_mono_l, N.add_le_mono; assumption.
      - rewrite Nat2N.inj_add. nia. }
    rewrite live_fold_lengths in Hfold. unfold live_graph_load.
    rewrite !Nat2N.inj_add in *. nia.
  Qed.

  Lemma live_intersection_atom : forall p defs old,
    incl defs (U.universe (R.prepare p)) ->
    (T_live_intersection defs old <=
      4 * live_clock_atom p * N.of_nat (length defs + 1))%N.
  Proof.
    intros p defs; induction defs as [|x rest IH]; intros old Hvars.
    - pose proof (live_clock_atom_positive p) as Hpositive. time_step.
    - pose proof (live_clock_atom_positive p) as Hpositive.
      pose proof (live_variable_key p x (Hvars x (or_introl eq_refl))) as Hx.
      specialize (IH old ltac:(intros y Hy; apply Hvars; now right)).
      pose proof (live_set_atom _ p x tt (live_intersection rest old) Hx) as Hset.
      time_unfold T_live_intersection. destruct old as [row|].
      + pose proof (live_member_atom p x row Hx) as Hmember.
        destruct (live_member x row); cbn [length]; rewrite !Nat2N.inj_add in *; nia.
      + cbn [length]; rewrite !Nat2N.inj_add in *; nia.
  Qed.

  Lemma live_kill_add_atom : forall p src dst defs table,
    (N.of_nat (Pos.size_nat src + 1) <= live_clock_scale * live_clock_width p)%N ->
    (N.of_nat (Pos.size_nat dst + 1) <= live_clock_scale * live_clock_width p)%N ->
    incl defs (U.universe (R.prepare p)) ->
    (T_live_kill_add src dst defs table <=
      16 * live_clock_atom p * N.of_nat (length defs + 1))%N.
  Proof.
    intros p src dst defs table Hsrc Hdst Hvars.
    pose proof (live_clock_atom_positive p) as Hpositive.
    pose proof (live_get_atom _ p dst table Hdst) as Hgetdst.
    time_unfold T_live_kill_add. destruct (trie_get dst table) as [row|].
    all: let defs := constr:(defs) in let src := constr:(src) in match goal with
      | |- context [T_live_intersection defs (trie_get src ?row)] =>
        pose proof (live_get_atom _ p src row Hsrc) as Hgetsrc;
        pose proof (live_intersection_atom p defs (trie_get src row) Hvars) as Hinter;
        pose proof (live_set_atom _ p src (live_intersection defs (trie_get src row))
          row Hsrc) as Hsetsrc;
        pose proof (live_set_atom _ p dst
          (PTrieCode.set src (live_intersection defs (trie_get src row)) row) table Hdst)
          as Hsetdst
      end; rewrite !Nat2N.inj_add in *; nia.
  Qed.

  Lemma reverse_index_atom : forall p es,
    incl es (C.edges (R.prepare p)) ->
    (T_reverse_index (R.prepare p) es <= 32 * live_clock_atom p *
      N.of_nat (length es + length (flat_map (U.defs (R.prepare p)) es) + 1))%N.
  Proof.
    intros p es Hlisted. set (q := R.prepare p).
    pose proof (proj2 (PB.prepared_wf p)) as Hwf.
    pose proof (live_clock_atom_positive p) as Hpositive.
    time_unfold T_reverse_index. fold q in Hlisted, Hwf |- *.
    let es := constr:(es) in match goal with
    | |- context [List.T_fold_right ?step ?clock Empty es] =>
      assert (Hfold : (List.T_fold_right step clock Empty es <=
        (24 * live_clock_atom p + 1) * N.of_nat
          (fold_right (fun e n => (length (U.defs q e) + 1 + n)%nat) 0%nat es) + 1)%N)
    end.
    { apply live_fold_clock_weight; [intros; lia|]. intros e He state; cbn beta.
      pose proof (Hlisted e He) as Hedge.
      destruct (C.edges_nodes q e Hwf Hedge) as [Hsrc Hdst].
      pose proof (live_src_atom p e) as Hsrcclock.
      pose proof (live_dst_atom p e) as Hdstclock.
      pose proof (live_encode_node_atom p (C.src q e) Hsrc) as Hsrcenc.
      pose proof (live_encode_node_atom p (C.dst q e) Hdst) as Hdstenc.
      pose proof (live_defs_atom p e Hedge) as Hreader.
      pose proof (live_kill_add_atom p (N.encode (C.src q e)) (N.encode (C.dst q e))
        (U.defs q e) state (live_node_key p (C.src q e) Hsrc)
        (live_node_key p (C.dst q e) Hdst)
        ltac:(intros x Hx; exact (live_defs_universe q e x Hedge Hx))) as Hkill.
      fold q in Hsrcclock, Hdstclock, Hreader.
      rewrite !Nat2N.inj_add in *. nia. }
    rewrite live_fold_lengths in Hfold. rewrite !Nat2N.inj_add in *. nia.
  Qed.

  Lemma reverse_kills_atom : forall p,
    (T_reverse_kills (R.prepare p) <=
      64 * live_clock_atom p * N.of_nat (live_graph_load (R.prepare p)))%N.
  Proof.
    intro p. pose proof (live_clock_atom_positive p) as Hpositive.
    pose proof (live_edges_atom p) as Hedges.
    pose proof (live_def_count (R.prepare p)) as Hdefs.
    pose proof (reverse_index_atom p (C.edges (R.prepare p)) (incl_refl _)) as Hreverse.
    time_unfold T_reverse_kills. unfold live_graph_load. rewrite !Nat2N.inj_add in *. nia.
  Qed.

  (** Edge deduplication charges each encoded edge identity once. *)
  Lemma incoming_discover_atom : forall p e st, In e (C.edges (R.prepare p)) ->
    (T_live_discover E.encode E.T_encode e st <= 16 * live_clock_atom p)%N.
  Proof.
    intros p e st He.
    pose proof (live_clock_atom_positive p) as Hpositive.
    pose proof (live_edge_key p e He) as Hkey.
    pose proof (live_encode_edge_atom p e He) as Hencode.
    pose proof (live_member_atom p (E.encode e) (live_seen st) Hkey) as Hmember.
    pose proof (live_set_atom _ p (E.encode e) tt (live_seen st) Hkey) as Hset.
    time_unfold @T_live_discover. time_unfold @T_live_discover_code. time_simpl.
    destruct (live_member (E.encode e) (live_seen st)); nia.
  Qed.

  (** Deduplicating the edge inventory takes linear work at the syntax key width. *)
  Lemma incoming_edges_atom : forall p,
    (T_incoming_edges (R.prepare p) <=
      24 * live_clock_atom p * N.of_nat (length (C.edges (R.prepare p)) + 1))%N.
  Proof.
    intro p. pose proof (live_clock_atom_positive p) as Hpositive.
    pose proof (live_edges_atom p) as Hedges.
    assert (Hinitial : (T_live_initial E.encode E.T_encode (C.edges (R.prepare p)) <=
      20 * live_clock_atom p * N.of_nat (length (C.edges (R.prepare p)) + 1))%N).
    { time_unfold @T_live_initial.
      let p := constr:(p) in match goal with
      | |- context [List.T_fold_right ?step ?clock ?initial (C.edges (R.prepare p))] =>
        assert (Hfold : (List.T_fold_right step clock initial (C.edges (R.prepare p)) <=
          (16 * live_clock_atom p + 1) * N.of_nat (length (C.edges (R.prepare p))) + 1)%N)
      end.
      { apply live_fold_clock_uniform. intros e He st. now apply incoming_discover_atom. }
      rewrite Nat2N.inj_add. nia. }
    time_unfold T_incoming_edges.
    change (1 + (C.T_edges (R.prepare p) +
      T_live_initial E.encode E.T_encode (C.edges (R.prepare p)) + 1) <=
      24 * live_clock_atom p * N.of_nat (length (C.edges (R.prepare p)) + 1))%N.
    rewrite Nat2N.inj_add in *. nia.
  Qed.

  (** Resolving an edge stores its source code and builds its definition set once. *)
  Lemma incoming_edge_atom : forall p e, In e (C.edges (R.prepare p)) ->
    (T_incoming_edge (R.prepare p) e <=
      16 * live_clock_atom p * N.of_nat (length (U.defs (R.prepare p) e) + 1))%N.
  Proof.
    intros p e He.
    pose proof (live_clock_atom_positive p) as Hpositive.
    pose proof (proj2 (PB.prepared_wf p)) as Hwf.
    pose proof (proj1 (C.edges_nodes (R.prepare p) e Hwf He)) as Hsrc.
    pose proof (live_src_atom p e) as Hsource.
    pose proof (live_encode_node_atom p (C.src (R.prepare p) e) Hsrc) as Hencode.
    pose proof (live_defs_atom p e He) as Hdefs.
    pose proof (live_intersection_atom p (U.defs (R.prepare p) e) None
      ltac:(intros x Hx; exact (live_defs_universe (R.prepare p) e x He Hx))) as Hset.
    time_unfold T_incoming_edge. rewrite Nat2N.inj_add in *. nia.
  Qed.

  (** Inserting a resolved edge pays for its destination key and definition occurrences. *)
  Lemma incoming_insert_atom : forall p e table, In e (C.edges (R.prepare p)) ->
    (T_incoming_insert (R.prepare p) e table <=
      24 * live_clock_atom p * N.of_nat (length (U.defs (R.prepare p) e) + 1))%N.
  Proof.
    intros p e table He.
    pose proof (live_clock_atom_positive p) as Hpositive.
    pose proof (proj2 (PB.prepared_wf p)) as Hwf.
    pose proof (proj2 (C.edges_nodes (R.prepare p) e Hwf He)) as Hdst.
    pose proof (live_dst_atom p e) as Htarget.
    pose proof (live_encode_node_atom p (C.dst (R.prepare p) e) Hdst) as Hencode.
    pose proof (live_node_key p (C.dst (R.prepare p) e) Hdst) as Hkey.
    pose proof (incoming_edge_atom p e He) as Hedge.
    pose proof (live_row_atom _ p table (N.encode (C.dst (R.prepare p) e)) Hkey) as Hrow.
    pose proof (live_set_atom _ p (N.encode (C.dst (R.prepare p) e))
      (incoming_edge (R.prepare p) e :: index_row table (N.encode (C.dst (R.prepare p) e)))
      table Hkey) as Hset.
    time_unfold T_incoming_insert. rewrite Nat2N.inj_add in *. nia.
  Qed.

  (** Cache construction scans only its edge list and its definition occurrences. *)
  Lemma incoming_build_atom : forall p es, incl es (C.edges (R.prepare p)) ->
    (T_incoming_build (R.prepare p) es <= 32 * live_clock_atom p *
      N.of_nat (length es + length (flat_map (U.defs (R.prepare p)) es) + 1))%N.
  Proof.
    intros p es Hedges. pose proof (live_clock_atom_positive p) as Hpositive.
    time_unfold T_incoming_build.
    let es := constr:(es) in match goal with
    | |- context [List.T_fold_right ?step ?clock Empty es] =>
      assert (Hfold : (List.T_fold_right step clock Empty es <=
        (24 * live_clock_atom p + 1) * N.of_nat
          (fold_right (fun e n => (length (U.defs (R.prepare p) e) + 1 + n)%nat) 0%nat es)
          + 1)%N)
    end.
    { apply live_fold_clock_weight; [intros; lia|].
      intros e He table. apply incoming_insert_atom. now apply Hedges. }
    rewrite live_fold_lengths in Hfold. rewrite !Nat2N.inj_add in *. nia.
  Qed.

  (** The eager cache is linear in listed edges, regardless of adjacency multiplicities. *)
  Lemma incoming_table_atom : forall p,
    (T_incoming_table (R.prepare p) <=
      128 * live_clock_atom p * N.of_nat (live_graph_load (R.prepare p)))%N.
  Proof.
    intro p. pose proof (live_clock_atom_positive p) as Hpositive.
    pose proof (incoming_edges_atom p) as Hedges.
    pose proof (incoming_build_atom p (incoming_edges (R.prepare p))
      ltac:(intros e He; now apply incoming_edges_spec)) as Hbuild.
    pose proof (incoming_edges_work (R.prepare p)) as Hwork.
    pose proof (live_def_count (R.prepare p)) as Hdefs.
    time_unfold T_incoming_table. unfold live_graph_load.
    rewrite !Nat2N.inj_add in *. nia.
  Qed.

  Lemma use_index_bound : forall p,
    (T_use_index (R.prepare p) <= live_index_budget * N.of_nat (function_size p + 1) *
      N.of_nat (function_width p + 1))%N.
  Proof.
    intro p. pose proof (use_index_atom p) as Hindex.
    pose proof (live_graph_load_bound p) as Hload.
    eapply N.le_trans; [exact Hindex|].
    eapply N.le_trans; [apply N.mul_le_mono_l; exact Hload|].
    unfold live_clock_atom, live_clock_width, live_index_budget. nia.
  Qed.

  Lemma kill_index_bound : forall p,
    (T_kill_index (R.prepare p) <= live_index_budget * N.of_nat (function_size p + 1) *
      N.of_nat (function_width p + 1))%N.
  Proof.
    intro p. pose proof (kill_index_atom p) as Hindex.
    pose proof (live_graph_load_bound p) as Hload.
    eapply N.le_trans; [exact Hindex|].
    eapply N.le_trans; [apply N.mul_le_mono_l; exact Hload|].
    unfold live_clock_atom, live_clock_width, live_index_budget. nia.
  Qed.

  (** This proof-only trace records expanded points; the producer does not construct it. *)
  Fixpoint live_trace (fuel : nat) (q : Q.t) (kills : ptrie (ptrie (ptrie unit)))
      (x : positive) (st : live_state N.t) : list N.t :=
    match fuel with
    | 0 => []
    | S rest =>
      match live_todo st with
      | [] => []
      | n :: pending => n :: live_trace rest q kills x
          (add_predecessors q kills x n (C.inc q n)
            {| live_seen := live_seen st; live_todo := pending; live_done := live_done st |})
      end
    end.

  Lemma live_discover_keep_processed : forall st n m,
    live_valid N.encode st -> In m (live_done st) -> ~ In m (live_todo st) ->
    In m (live_done (live_discover N.encode n st)) /\
      ~ In m (live_todo (live_discover N.encode n st)).
  Proof.
    intros st n m Hvalid Hdone Htodo. split.
    - apply live_discover_done; [exact Hvalid|now right].
    - rewrite live_discover_todo by exact Hvalid.
      intros [[-> Hfresh]|Hin]; contradiction.
  Qed.

  (** Processing cached edges cannot requeue a point that has already been processed. *)
  Lemma cached_rows_keep_processed : forall x les st m,
    (forall le, In le les -> live_pred_code le = N.encode (live_pred le)) ->
    live_valid N.encode st -> In m (live_done st) -> ~ In m (live_todo st) ->
    In m (live_done (fold_right (cached_step x) st les)) /\
      ~ In m (live_todo (fold_right (cached_step x) st les)).
  Proof.
    intros x les; induction les as [|le rest IH]; intros st m Hcodes Hvalid Hdone Htodo;
      cbn [fold_right]; [now split|].
    assert (Htailcodes : forall item, In item rest ->
      live_pred_code item = N.encode (live_pred item)).
    { intros item Hin; apply Hcodes; now right. }
    destruct (IH st m Htailcodes Hvalid Hdone Htodo) as [Hdone' Htodo'].
    unfold cached_step. destruct (live_member x (live_defs le)); [now split|].
    rewrite (Hcodes le (or_introl eq_refl)).
    apply live_discover_keep_processed; [now apply cached_rows_valid|assumption|assumption].
  Qed.

  (** A complete cached predecessor row also preserves already processed points. *)
  Lemma cached_predecessors_keep_processed : forall q x n st m, C.wf q ->
    live_valid N.encode st -> In m (live_done st) -> ~ In m (live_todo st) ->
    In m (live_done (cached_predecessors (incoming_table q) x n st)) /\
      ~ In m (live_todo (cached_predecessors (incoming_table q) x n st)).
  Proof.
    intros q x n st m Hwf Hvalid Hdone Htodo. unfold cached_predecessors.
    apply cached_rows_keep_processed; [now apply incoming_table_codes|assumption|assumption|assumption].
  Qed.

  (** This proof-only trace records expanded points of the cached search. *)
  Fixpoint cached_trace (fuel : nat) (table : ptrie (list (live_edge N.t)))
      (x : positive) (st : live_state N.t) : list N.t :=
    match fuel with
    | 0 => []
    | S rest =>
      match live_todo st with
      | [] => []
      | n :: pending => n :: cached_trace rest table x
          (cached_predecessors table x n
            {| live_seen := live_seen st; live_todo := pending; live_done := live_done st |})
      end
    end.

  Lemma cached_trace_excludes : forall fuel q x st m, C.wf q ->
    live_valid N.encode st -> In m (live_done st) -> ~ In m (live_todo st) ->
    ~ In m (cached_trace fuel (incoming_table q) x st).
  Proof.
    induction fuel as [|fuel IH]; intros q x st m Hwf Hvalid Hdone Htodo;
      cbn [cached_trace]; [tauto|].
    destruct (live_todo st) as [|n pending] eqn:Hpending; [tauto|].
    intros [Heq|Hin].
    - subst m. apply Htodo. now left.
    - assert (Hpop := live_pop_valid st n pending Hvalid Hpending).
      assert (Hnot : ~ In m pending).
      { intro Hm; apply Htodo. now right. }
      destruct (cached_predecessors_keep_processed q x n
        {| live_seen := live_seen st; live_todo := pending; live_done := live_done st |}
        m Hwf Hpop Hdone Hnot) as [Hdone' Htodo'].
      eapply (IH q x (cached_predecessors (incoming_table q) x n
        {| live_seen := live_seen st; live_todo := pending; live_done := live_done st |}) m).
      + exact Hwf.
      + apply cached_predecessors_valid; assumption.
      + exact Hdone'.
      + exact Htodo'.
      + exact Hin.
  Qed.

  Lemma cached_trace_nodup : forall fuel q x st, C.wf q ->
    live_valid N.encode st -> NoDup (cached_trace fuel (incoming_table q) x st).
  Proof.
    induction fuel as [|fuel IH]; intros q x st Hwf Hvalid;
      cbn [cached_trace]; [constructor|].
    destruct (live_todo st) as [|n pending] eqn:Hpending; [constructor|].
    assert (Hpop := live_pop_valid st n pending Hvalid Hpending).
    assert (Hnext : live_valid N.encode (cached_predecessors (incoming_table q) x n
      {| live_seen := live_seen st; live_todo := pending; live_done := live_done st |})).
    { apply cached_predecessors_valid; assumption. }
    constructor; [|now apply IH].
    assert (Hdone : In n (live_done st)).
    { apply (proj2 (proj2 (proj2 Hvalid))). rewrite Hpending; now left. }
    assert (Hnot : ~ In n pending).
    { pose proof (proj1 (proj2 (proj2 Hvalid))) as Hdup.
      rewrite Hpending in Hdup. now inversion Hdup. }
    destruct (cached_predecessors_keep_processed q x n
      {| live_seen := live_seen st; live_todo := pending; live_done := live_done st |}
      n Hwf Hpop Hdone Hnot) as [Hdone' Htodo'].
    eapply cached_trace_excludes; eassumption.
  Qed.

  Lemma cached_trace_sound : forall fuel q x st,
    C.wf q -> live_valid N.encode st -> live_sound q x st ->
    forall n, In n (cached_trace fuel (incoming_table q) x st) ->
      In n (C.nodes q) /\
      point_live (C.nodes q) (C.out q) (C.dst q) (U.uses q) (U.defs q) (U.exits q) x n.
  Proof.
    induction fuel as [|fuel IH]; intros q x st Hwf Hvalid Hsound m Hin;
      cbn [cached_trace] in Hin; [contradiction|].
    destruct (live_todo st) as [|n pending] eqn:Hpending; [contradiction|].
    destruct Hin as [<-|Hin].
    - apply Hsound. apply (proj2 (proj2 (proj2 Hvalid))). rewrite Hpending; now left.
    - eapply (IH q x (cached_predecessors (incoming_table q) x n
        {| live_seen := live_seen st; live_todo := pending; live_done := live_done st |}) Hwf).
      + apply cached_predecessors_valid; [exact Hwf|]. eapply live_pop_valid; eassumption.
      + eapply cached_step_sound; eassumption.
      + exact Hin.
  Qed.

  Lemma add_predecessors_keep_processed : forall q kills x n es st m,
    live_valid N.encode st -> In m (live_done st) -> ~ In m (live_todo st) ->
    In m (live_done (add_predecessors q kills x n es st)) /\
      ~ In m (live_todo (add_predecessors q kills x n es st)).
  Proof.
    intros q kills x n es; induction es as [|e rest IH]; intros st m Hvalid Hdone Htodo.
    - now split.
    - cbn [add_predecessors fold_right]. fold (add_predecessors q kills x n rest st).
      destruct (live_killed kills (N.encode (C.src q e)) (N.encode n) x).
      + now apply IH.
      + destruct (IH st m Hvalid Hdone Htodo) as [Hdone' Htodo'].
        apply live_discover_keep_processed; [now apply
          add_predecessors_valid|assumption|assumption].
  Qed.

  Lemma live_trace_excludes : forall fuel q kills x st m,
    live_valid N.encode st -> In m (live_done st) -> ~ In m (live_todo st) ->
    ~ In m (live_trace fuel q kills x st).
  Proof.
    induction fuel as [|fuel IH]; intros q kills x st m Hvalid Hdone Htodo;
      cbn [live_trace]; [tauto|].
    destruct (live_todo st) as [|n pending] eqn:Hpending; [tauto|].
    intros [Heq|Hin].
    - subst m. apply Htodo. now left.
    - assert (Hpop := live_pop_valid st n pending Hvalid Hpending).
      assert (Hnot : ~ In m pending).
      { intro Hm; apply Htodo. now right. }
      destruct (add_predecessors_keep_processed q kills x n (C.inc q n)
        {| live_seen := live_seen st; live_todo := pending; live_done := live_done st |}
        m Hpop Hdone Hnot) as [Hdone' Htodo'].
      eapply (IH q kills x (add_predecessors q kills x n (C.inc q n)
        {| live_seen := live_seen st; live_todo := pending; live_done := live_done st |}) m).
      + apply add_predecessors_valid; exact Hpop.
      + exact Hdone'.
      + exact Htodo'.
      + exact Hin.
  Qed.

  Lemma live_trace_nodup : forall fuel q kills x st,
    live_valid N.encode st -> NoDup (live_trace fuel q kills x st).
  Proof.
    induction fuel as [|fuel IH]; intros q kills x st Hvalid;
      cbn [live_trace]; [constructor|].
    destruct (live_todo st) as [|n pending] eqn:Hpending; [constructor|].
    assert (Hpop := live_pop_valid st n pending Hvalid Hpending).
    assert (Hnext : live_valid N.encode (add_predecessors q kills x n (C.inc q n)
      {| live_seen := live_seen st; live_todo := pending; live_done := live_done st |})).
    { now apply add_predecessors_valid. }
    constructor; [|now apply IH].
    assert (Hdone : In n (live_done st)).
    { apply (proj2 (proj2 (proj2 Hvalid))). rewrite Hpending; now left. }
    assert (Hnot : ~ In n pending).
    { pose proof (proj1 (proj2 (proj2 Hvalid))) as Hdup.
      rewrite Hpending in Hdup. now inversion Hdup. }
    destruct (add_predecessors_keep_processed q kills x n (C.inc q n)
      {| live_seen := live_seen st; live_todo := pending; live_done := live_done st |}
      n Hpop Hdone Hnot) as [Hdone' Htodo'].
    eapply live_trace_excludes; eassumption.
  Qed.

  Lemma live_trace_sound : forall fuel q x st,
    C.wf q -> live_valid N.encode st -> live_sound q x st ->
    forall n, In n (live_trace fuel q (reverse_kills q) x st) ->
      In n (C.nodes q) /\
      point_live (C.nodes q) (C.out q) (C.dst q) (U.uses q) (U.defs q) (U.exits q) x n.
  Proof.
    induction fuel as [|fuel IH]; intros q x st Hwf Hvalid Hsound m Hin;
      cbn [live_trace] in Hin; [contradiction|].
    destruct (live_todo st) as [|n pending] eqn:Hpending; [contradiction|].
    destruct Hin as [<-|Hin].
    - apply Hsound. apply (proj2 (proj2 (proj2 Hvalid))). rewrite Hpending; now left.
    - eapply (IH q x (add_predecessors q (reverse_kills q) x n (C.inc q n)
        {| live_seen := live_seen st; live_todo := pending; live_done := live_done st |}) Hwf).
      + apply add_predecessors_valid. eapply live_pop_valid; eassumption.
      + eapply live_step_sound; eassumption.
      + exact Hin.
  Qed.

  Definition live_trace_work (q : Q.t) (ns : list N.t) : nat :=
    fold_right (fun n amount => 1 + length (C.inc q n) + amount) 0 ns.

  Lemma live_trace_map : forall q (x : positive) ns,
    fold_right (fun pair amount => 1 + length (C.inc q (fst pair)) + amount) 0
      (map (fun n => (n, x)) ns) = live_trace_work q ns.
  Proof.
    intros q x ns; induction ns as [|n rest IH]; [reflexivity|].
    change (1 + length (C.inc q n) +
      fold_right (fun pair amount => 1 + length (C.inc q (fst pair)) + amount) 0
        (map (fun m => (m, x)) rest) =
      1 + length (C.inc q n) + live_trace_work q rest).
    now rewrite IH.
  Qed.

  Lemma live_point_charge : forall p x ns,
    NoDup ns -> (forall n, In n ns -> In (n, x) (live_region p)) ->
    live_trace_work (R.prepare p) ns <= variable_work p x.
  Proof.
    intros p x ns Hdup Hregion.
    pose proof (live_weighted_incl (N.t * positive)
      (fun pair => 1 + length (C.inc (R.prepare p) (fst pair)))
      (map (fun n => (n, x)) ns) (visits p x)
      (live_pair_row_nodup N.t ns x Hdup)) as Hweight.
    assert (Hincl : incl (map (fun n => (n, x)) ns) (visits p x)).
    { intros pair Hin. apply in_map_iff in Hin. destruct Hin as [n [<- Hn]].
      unfold visits. apply filter_In. split; [now apply Hregion|].
      cbn; apply Pos.eqb_refl. }
    specialize (Hweight Hincl).
    change (fold_right (fun pair amount =>
      1 + length (C.inc (R.prepare p) (fst pair)) + amount) 0
      (map (fun n => (n, x)) ns) <= variable_work p x) in Hweight.
    rewrite live_trace_map in Hweight. exact Hweight.
  Qed.

  Lemma live_trace_charge : forall p x fuel st,
    In x (U.universe (R.prepare p)) -> live_valid N.encode st ->
    live_sound (R.prepare p) x st ->
    live_trace_work (R.prepare p)
      (live_trace fuel (R.prepare p) (reverse_kills (R.prepare p)) x st) <= variable_work p x.
  Proof.
    intros p x fuel st Hx Hvalid Hsound. apply live_point_charge.
    - now apply live_trace_nodup.
    - intros n Hin. apply (proj2 (live_region_spec p) n x).
      destruct (live_trace_sound fuel (R.prepare p) x st
        (proj2 (PB.prepared_wf p)) Hvalid Hsound n Hin) as [Hnode Hlive].
      repeat split; assumption.
  Qed.

  Lemma live_points_length : forall q ns, length ns <= live_trace_work q ns.
  Proof.
    intros q ns; unfold live_trace_work. induction ns as [|n rest IH]; cbn in *; lia.
  Qed.

  Lemma live_seed_charge : forall p x,
    length (index_row (seed_index (R.prepare p)) x) <= variable_work p x.
  Proof.
    intros p x. eapply Nat.le_trans; [apply live_points_length|].
    apply live_point_charge; [apply seed_index_nodup|].
    intros n Hn. exact (proj2 (use_index_spec p x) n Hn).
  Qed.

  Lemma live_search_charge : forall p x,
    In x (U.universe (R.prepare p)) ->
    length (search (length (C.nodes (R.prepare p))) (R.prepare p)
      (seed_index (R.prepare p)) (reverse_kills (R.prepare p)) x) <= variable_work p x.
  Proof.
    intros p x Hx. eapply Nat.le_trans; [apply live_points_length|].
    pose proof (search_spec (R.prepare p) x (proj2 (PB.prepared_wf p))) as [Hdup Hspec].
    apply live_point_charge; [exact Hdup|]. intros n Hin.
    apply (proj2 (live_region_spec p) n x). apply Hspec in Hin; tauto.
  Qed.

  Lemma cached_trace_charge : forall p x fuel st,
    In x (U.universe (R.prepare p)) -> live_valid N.encode st ->
    live_sound (R.prepare p) x st ->
    live_trace_work (R.prepare p)
      (cached_trace fuel (incoming_table (R.prepare p)) x st) <= variable_work p x.
  Proof.
    intros p x fuel st Hx Hvalid Hsound. apply live_point_charge.
    - apply cached_trace_nodup; [exact (proj2 (PB.prepared_wf p))|exact Hvalid].
    - intros n Hin. apply (proj2 (live_region_spec p) n x).
      destruct (cached_trace_sound fuel (R.prepare p) x st
        (proj2 (PB.prepared_wf p)) Hvalid Hsound n Hin) as [Hnode Hlive].
      repeat split; assumption.
  Qed.

  Lemma cached_search_charge : forall p x,
    In x (U.universe (R.prepare p)) ->
    length (cached_search (length (C.nodes (R.prepare p)))
      (seed_index (R.prepare p)) (incoming_table (R.prepare p)) x) <= variable_work p x.
  Proof.
    intros p x Hx. eapply Nat.le_trans; [apply live_points_length|].
    apply live_point_charge.
    - apply cached_search_nodup. exact (proj2 (PB.prepared_wf p)).
    - intros n Hin. apply (proj2 (live_region_spec p) n x).
      destruct (cached_search_live (R.prepare p) x n (proj2 (PB.prepared_wf p)) Hin)
        as [Hnode Hlive]. repeat split; assumption.
  Qed.

  (** Each expansion pays for its bounded keys and actual incoming incidences. *)
  Lemma live_kill_row_atom : forall p table src dst,
    (N.of_nat (Pos.size_nat src + 1) <= live_clock_scale * live_clock_width p)%N ->
    (N.of_nat (Pos.size_nat dst + 1) <= live_clock_scale * live_clock_width p)%N ->
    (T_live_kill_row table src dst <= 3 * live_clock_atom p)%N.
  Proof.
    intros p table src dst Hsrc Hdst.
    pose proof (live_clock_atom_positive p) as Hpositive.
    pose proof (live_get_atom _ p dst table Hdst) as Hgetdst.
    time_unfold T_live_kill_row. destruct (trie_get dst table) as [row|]; [|nia].
    pose proof (live_get_atom _ p src row Hsrc) as Hgetsrc. nia.
  Qed.

  Lemma live_killed_atom : forall p table src dst x,
    (N.of_nat (Pos.size_nat src + 1) <= live_clock_scale * live_clock_width p)%N ->
    (N.of_nat (Pos.size_nat dst + 1) <= live_clock_scale * live_clock_width p)%N ->
    In x (U.universe (R.prepare p)) ->
    (T_live_killed table src dst x <= 5 * live_clock_atom p)%N.
  Proof.
    intros p table src dst x Hsrc Hdst Hx.
    pose proof (live_clock_atom_positive p) as Hpositive.
    pose proof (live_kill_row_atom p table src dst Hsrc Hdst) as Hrow.
    time_unfold T_live_killed. destruct (live_kill_row table src dst) as [defs|]; [|nia].
    pose proof (live_member_atom p x defs (live_variable_key p x Hx)) as Hmember. nia.
  Qed.

  (** Discovery reuses the encoded point for its membership test and insertion. *)
  Lemma live_discover_code_atom : forall p n st,
    In n (C.nodes (R.prepare p)) ->
    (T_live_discover_code (N.encode n) n st <= 8 * live_clock_atom p)%N.
  Proof.
    intros p n st Hn.
    pose proof (live_clock_atom_positive p) as Hpositive.
    pose proof (live_node_key p n Hn) as Hkey.
    pose proof (live_member_atom p (N.encode n) (live_seen st) Hkey) as Hmember.
    pose proof (live_set_atom _ p (N.encode n) tt (live_seen st) Hkey) as Hset.
    time_unfold @T_live_discover_code. time_simpl.
    destruct (live_member (N.encode n) (live_seen st)); nia.
  Qed.

  Lemma live_discover_atom : forall p n st,
    In n (C.nodes (R.prepare p)) ->
    (T_live_discover N.encode N.T_encode n st <= 16 * live_clock_atom p)%N.
  Proof.
    intros p n st Hn.
    pose proof (live_clock_atom_positive p) as Hpositive.
    pose proof (live_encode_node_atom p n Hn) as Hencode.
    pose proof (live_discover_code_atom p n st Hn) as Hdiscover.
    time_unfold @T_live_discover. nia.
  Qed.

  Lemma live_initial_atom : forall p seeds,
    incl seeds (C.nodes (R.prepare p)) ->
    (T_live_initial N.encode N.T_encode seeds <=
      20 * live_clock_atom p * N.of_nat (length seeds + 1))%N.
  Proof.
    intros p seeds Hseeds. pose proof (live_clock_atom_positive p) as Hpositive.
    time_unfold @T_live_initial.
    let seeds := constr:(seeds) in match goal with
    | |- context [List.T_fold_right ?step ?clock ?initial seeds] =>
      assert (Hfold : (List.T_fold_right step clock initial seeds <=
        (16 * live_clock_atom p + 1) * N.of_nat (length seeds) + 1)%N)
    end.
    { apply live_fold_clock_uniform. intros n Hn st. apply live_discover_atom; now apply Hseeds. }
    rewrite Nat2N.inj_add. nia.
  Qed.

  (** A cached edge expansion performs one definition-membership check and discovery. *)
  Lemma cached_step_atom : forall p x n le st,
    In x (U.universe (R.prepare p)) ->
    In le (index_row (incoming_table (R.prepare p)) (N.encode n)) ->
    (T_cached_step x le st <= 16 * live_clock_atom p)%N.
  Proof.
    intros p x n le st Hx Hle.
    pose proof (live_clock_atom_positive p) as Hpositive.
    pose proof (proj2 (PB.prepared_wf p)) as Hwf.
    apply (incoming_table_member (R.prepare p) n le Hwf) in Hle.
    destruct Hle as [e [He ->]]. apply (C.inc_spec _ _ _ Hwf) in He.
    pose proof (proj1 (C.edges_nodes (R.prepare p) e Hwf (proj1 He))) as Hsrc.
    pose proof (live_discover_code_atom p (C.src (R.prepare p) e) st Hsrc) as Hdiscover.
    pose proof (live_member_atom p x (live_defs (incoming_edge (R.prepare p) e))
      (live_variable_key p x Hx)) as Hmember.
    time_unfold T_cached_step. time_simpl.
    rewrite incoming_edge_code, incoming_edge_pred.
    destruct (live_member x (live_defs (incoming_edge (R.prepare p) e))); nia.
  Qed.

  (** Reading a cached row pays for its point key and no more than its public incidence count. *)
  Lemma cached_predecessors_atom : forall p x n st,
    In x (U.universe (R.prepare p)) -> In n (C.nodes (R.prepare p)) ->
    (T_cached_predecessors (incoming_table (R.prepare p)) x n st <=
      32 * live_clock_atom p * N.of_nat (length (C.inc (R.prepare p) n) + 1))%N.
  Proof.
    intros p x n st Hx Hn.
    pose proof (live_clock_atom_positive p) as Hpositive.
    pose proof (live_encode_node_atom p n Hn) as Hencode.
    pose proof (live_row_atom _ p (incoming_table (R.prepare p)) (N.encode n)
      (live_node_key p n Hn)) as Hrow.
    pose proof (incoming_table_length (R.prepare p) n (proj2 (PB.prepared_wf p))) as Hlength.
    time_unfold T_cached_predecessors.
    let st := constr:(st) in match goal with
    | |- context [List.T_fold_right ?step ?clock st ?row] =>
      assert (Hfold : (List.T_fold_right step clock st row <=
        (16 * live_clock_atom p + 1) * N.of_nat (length row) + 1)%N)
    end.
    { apply live_fold_clock_uniform. intros le Hle state. now apply cached_step_atom with n. }
    rewrite !Nat2N.inj_add in *. nia.
  Qed.

  Lemma cached_fuel_atom : forall fuel p x st,
    In x (U.universe (R.prepare p)) -> live_valid N.encode st ->
    live_sound (R.prepare p) x st ->
    (T_cached_fuel fuel (incoming_table (R.prepare p)) x st <=
      64 * live_clock_atom p * N.of_nat
        (live_trace_work (R.prepare p)
          (cached_trace fuel (incoming_table (R.prepare p)) x st) + 1))%N.
  Proof.
    induction fuel as [|fuel IH]; intros p x st Hx Hvalid Hsound.
    - pose proof (live_clock_atom_positive p) as Hpositive. time_step.
    - pose proof (live_clock_atom_positive p) as Hpositive.
      pose proof (proj2 (PB.prepared_wf p)) as Hwf.
      time_unfold T_cached_fuel. time_simpl.
      cbn [cached_trace]. destruct (live_todo st) as [|n pending] eqn:Hpending.
      + cbn [live_trace_work fold_right]. nia.
      + set (next := cached_predecessors (incoming_table (R.prepare p)) x n
          {| live_seen := live_seen st; live_todo := pending; live_done := live_done st |}).
        assert (Hnext : live_valid N.encode next).
        { apply cached_predecessors_valid; [exact Hwf|]. eapply live_pop_valid; eassumption. }
        assert (Hnextsound : live_sound (R.prepare p) x next).
        { eapply cached_step_sound; eassumption. }
        specialize (IH p x next Hx Hnext Hnextsound).
        assert (Hnode : In n (C.nodes (R.prepare p))).
        { assert (Hdone : In n (live_done st)).
          { apply (proj2 (proj2 (proj2 Hvalid))). rewrite Hpending; now left. }
          exact (proj1 (Hsound n Hdone)). }
        pose proof (cached_predecessors_atom p x n
          {| live_seen := live_seen st; live_todo := pending; live_done := live_done st |}
          Hx Hnode) as Hpred.
        fold next. change (1 + (1 + ((1 + 1) +
          T_cached_predecessors (incoming_table (R.prepare p)) x n
            {| live_seen := live_seen st; live_todo := pending; live_done := live_done st |}
          + T_cached_fuel fuel (incoming_table (R.prepare p)) x next)) <=
          64 * live_clock_atom p * N.of_nat
            (1 + length (C.inc (R.prepare p) n) +
              live_trace_work (R.prepare p)
                (cached_trace fuel (incoming_table (R.prepare p)) x next) + 1))%N.
        rewrite !Nat2N.inj_add in *. nia.
  Qed.

  Lemma cached_search_atom : forall p x, In x (U.universe (R.prepare p)) ->
    (T_cached_search (length (C.nodes (R.prepare p)))
      (seed_index (R.prepare p)) (incoming_table (R.prepare p)) x <=
      128 * live_clock_atom p * N.of_nat (variable_work p x + 1))%N.
  Proof.
    intros p x Hx. set (q := R.prepare p).
    set (initial := live_initial N.encode (index_row (seed_index q) x)).
    pose proof (live_clock_atom_positive p) as Hpositive.
    pose proof (proj2 (PB.prepared_wf p)) as Hwf.
    assert (Hvalid : live_valid N.encode initial).
    { apply live_initial_valid; exact N.encode_inj. }
    assert (Hsound : live_sound q x initial).
    { intros n Hn. apply live_initial_done in Hn; [|exact N.encode_inj].
      destruct (seed_index_live q x n Hwf Hn) as [Hnode [_ Hlive]]; now split. }
    pose proof (cached_trace_charge p x (length (C.nodes q)) initial Hx Hvalid Hsound) as Hcharge.
    pose proof (cached_fuel_atom (length (C.nodes q)) p x initial Hx Hvalid Hsound) as Hfuel.
    pose proof (live_seed_charge p x) as Hseeds.
    pose proof (live_initial_atom p (index_row (seed_index q) x)
      ltac:(intros n Hn; exact (proj1 (seed_index_live q x n Hwf Hn)))) as Hinitial.
    pose proof (live_row_atom _ p (seed_index q) x (live_variable_key p x Hx)) as Hrow.
    time_unfold T_cached_search. time_simpl. fold q initial.
    fold q in Hcharge, Hfuel, Hseeds, Hinitial, Hrow.
    change (1 + (T_index_row (seed_index q) x +
      T_live_initial N.encode N.T_encode (index_row (seed_index q) x) +
      T_cached_fuel (length (C.nodes q)) (incoming_table q) x initial + 1) <=
      128 * live_clock_atom p * N.of_nat (variable_work p x + 1))%N.
    rewrite !Nat2N.inj_add in *. nia.
  Qed.

  Lemma add_predecessors_atom : forall p kills x n es st,
    In x (U.universe (R.prepare p)) -> In n (C.nodes (R.prepare p)) ->
    incl es (C.edges (R.prepare p)) ->
    (T_add_predecessors (R.prepare p) kills x n es st <=
      48 * live_clock_atom p * N.of_nat (length es + 1))%N.
  Proof.
    intros p kills x n es st Hx Hn Hes.
    pose proof (live_clock_atom_positive p) as Hpositive.
    pose proof (proj2 (PB.prepared_wf p)) as Hwf.
    pose proof (live_encode_node_atom p n Hn) as Hnenc.
    time_unfold T_add_predecessors. cbn beta zeta.
    let st := constr:(st) in let es := constr:(es) in match goal with
    | |- context [List.T_fold_right ?step ?clock st es] =>
      assert (Hfold : (List.T_fold_right step clock st es <=
        (32 * live_clock_atom p + 1) * N.of_nat (length es) + 1)%N)
    end.
    { apply live_fold_clock_uniform. intros e He state; cbn beta zeta.
      pose proof (proj1 (C.edges_nodes (R.prepare p) e Hwf (Hes e He))) as Hsrc.
      pose proof (live_src_atom p e) as Hsrcclock.
      pose proof (live_encode_node_atom p (C.src (R.prepare p) e) Hsrc) as Hpredenc.
      pose proof (live_killed_atom p kills (N.encode (C.src (R.prepare p) e)) (N.encode n) x
        (live_node_key p (C.src (R.prepare p) e) Hsrc) (live_node_key p n Hn) Hx) as Hkilled.
      pose proof (live_discover_code_atom p (C.src (R.prepare p) e) state Hsrc) as Hdiscover.
      destruct (live_killed kills (N.encode (C.src (R.prepare p) e)) (N.encode n) x); nia. }
    rewrite Nat2N.inj_add. nia.
  Qed.

  Lemma explore_fuel_atom : forall fuel p x st,
    In x (U.universe (R.prepare p)) -> live_valid N.encode st ->
    live_sound (R.prepare p) x st ->
    (T_explore_fuel fuel (R.prepare p) (reverse_kills (R.prepare p)) x st <=
      64 * live_clock_atom p * N.of_nat
        (live_trace_work (R.prepare p)
          (live_trace fuel (R.prepare p) (reverse_kills (R.prepare p)) x st) + 1))%N.
  Proof.
    induction fuel as [|fuel IH]; intros p x st Hx Hvalid Hsound.
    - pose proof (live_clock_atom_positive p) as Hpositive. time_step.
    - pose proof (live_clock_atom_positive p) as Hpositive.
      pose proof (proj2 (PB.prepared_wf p)) as Hwf.
      time_unfold T_explore_fuel. time_simpl.
      cbn [live_trace]. destruct (live_todo st) as [|n pending] eqn:Hpending.
      + cbn [live_trace_work fold_right]. nia.
      + set (next := add_predecessors (R.prepare p) (reverse_kills (R.prepare p)) x n
          (C.inc (R.prepare p) n)
          {| live_seen := live_seen st; live_todo := pending; live_done := live_done st |}).
        assert (Hnext : live_valid N.encode next).
        { apply add_predecessors_valid. eapply live_pop_valid; eassumption. }
        assert (Hnextsound : live_sound (R.prepare p) x next).
        { eapply live_step_sound; eassumption. }
        specialize (IH p x next Hx Hnext Hnextsound).
        assert (Hnode : In n (C.nodes (R.prepare p))).
        { assert (Hdone : In n (live_done st)).
          { apply (proj2 (proj2 (proj2 Hvalid))). rewrite Hpending; now left. }
          exact (proj1 (Hsound n Hdone)). }
        pose proof (live_inc_atom p n Hnode) as Hinc.
        pose proof (add_predecessors_atom p (reverse_kills (R.prepare p)) x n
          (C.inc (R.prepare p) n)
          {| live_seen := live_seen st; live_todo := pending; live_done := live_done st |}
          Hx Hnode ltac:(intros e He; exact (proj1 (proj1 (C.inc_spec _ _ _ Hwf) He))))
          as Hpred.
        fold next. change (1 + (1 + (C.T_inc (R.prepare p) n + (1 + 1) +
          T_add_predecessors (R.prepare p) (reverse_kills (R.prepare p)) x n
            (C.inc (R.prepare p) n)
            {| live_seen := live_seen st; live_todo := pending; live_done := live_done st |}
          + T_explore_fuel fuel (R.prepare p) (reverse_kills (R.prepare p)) x next)) <=
          64 * live_clock_atom p * N.of_nat
            (1 + length (C.inc (R.prepare p) n) +
              live_trace_work (R.prepare p)
                (live_trace fuel (R.prepare p) (reverse_kills (R.prepare p)) x next) + 1))%N.
        rewrite !Nat2N.inj_add in *. nia.
  Qed.

  Lemma search_atom : forall p x, In x (U.universe (R.prepare p)) ->
    (T_search (length (C.nodes (R.prepare p))) (R.prepare p)
      (seed_index (R.prepare p)) (reverse_kills (R.prepare p)) x <=
      128 * live_clock_atom p * N.of_nat (variable_work p x + 1))%N.
  Proof.
    intros p x Hx. set (q := R.prepare p).
    set (initial := live_initial N.encode (index_row (seed_index q) x)).
    pose proof (live_clock_atom_positive p) as Hpositive.
    pose proof (proj2 (PB.prepared_wf p)) as Hwf.
    assert (Hvalid : live_valid N.encode initial).
    { apply live_initial_valid; exact N.encode_inj. }
    assert (Hsound : live_sound q x initial).
    { intros n Hn. apply live_initial_done in Hn; [|exact N.encode_inj].
      destruct (seed_index_live q x n Hwf Hn) as [Hnode [_ Hlive]]; now split. }
    pose proof (live_trace_charge p x (length (C.nodes q)) initial Hx Hvalid Hsound) as Hcharge.
    pose proof (explore_fuel_atom (length (C.nodes q)) p x initial Hx Hvalid Hsound) as Hfuel.
    pose proof (live_seed_charge p x) as Hseeds.
    pose proof (live_initial_atom p (index_row (seed_index q) x)
      ltac:(intros n Hn; exact (proj1 (seed_index_live q x n Hwf Hn)))) as Hinitial.
    pose proof (live_row_atom _ p (seed_index q) x (live_variable_key p x Hx)) as Hrow.
    time_unfold T_search. time_simpl. fold q initial.
    fold q in Hcharge, Hfuel, Hseeds, Hinitial, Hrow.
    change (1 + (T_index_row (seed_index q) x +
      T_live_initial N.encode N.T_encode (index_row (seed_index q) x) +
      T_explore_fuel (length (C.nodes q)) q (reverse_kills q) x initial + 1) <=
      128 * live_clock_atom p * N.of_nat (variable_work p x + 1))%N.
    rewrite !Nat2N.inj_add in *. nia.
  Qed.

  Lemma block_index_binding : forall bs key value,
    trie_get key (block_index bs) = Some value -> In value bs /\ key = value.
  Proof.
    intro bs; induction bs as [|b rest IH]; intros key value Hget.
    - unfold block_index in Hget; cbn [fold_right] in Hget.
      rewrite PTrie.get_empty in Hget; discriminate.
    - cbn [block_index fold_right] in Hget. fold (block_index rest) in Hget.
      destruct (Pos.eq_dec key b) as [->|Hneq].
      + rewrite PTrie.get_set_same in Hget. inversion Hget; subst; split; [now left|reflexivity].
      + rewrite PTrie.get_set_other in Hget by exact Hneq.
        destruct (IH key value Hget) as [Hin Heq]. split; [now right|exact Heq].
  Qed.

  Lemma block_index_height : forall p,
    live_height (block_index (BC.nodes (R.prepare p))) <= function_width p.
  Proof.
    intro p. apply live_height_bound. intros key value Hget.
    destruct (block_index_binding _ _ _ Hget) as [Hin ->].
    exact (PB.block_bits_le p value (or_introl Hin)).
  Qed.

  Lemma block_lookup_atom : forall p key,
    (T_live_lookup key (block_index (BC.nodes (R.prepare p))) <= live_clock_atom p)%N.
  Proof.
    intros p key. pose proof (T_live_lookup_bound positive key
      (block_index (BC.nodes (R.prepare p)))) as Hlookup.
    pose proof (block_index_height p) as Hheight.
    pose proof live_clock_scale_positive as Hscale.
    unfold live_clock_atom, live_clock_width. nia.
  Qed.

  Lemma block_index_atom : forall p,
    (T_block_index (BC.nodes (R.prepare p)) <=
      4 * live_clock_atom p * N.of_nat (length (BC.nodes (R.prepare p)) + 1))%N.
  Proof.
    intro p. pose proof (live_clock_atom_positive p) as Hpositive.
    time_unfold T_block_index.
    let p := constr:(p) in match goal with
    | |- context [List.T_fold_right ?step ?clock Empty (BC.nodes (R.prepare p))] =>
      assert (Hfold : (List.T_fold_right step clock Empty (BC.nodes (R.prepare p)) <=
        (2 * live_clock_atom p + 1) * N.of_nat (length (BC.nodes (R.prepare p))) + 1)%N)
    end.
    { apply live_fold_clock_uniform; intros b Hb table; cbn beta.
      pose proof (live_set_atom _ p b b table (live_block_key p b Hb)) as Hset.
      change (1 + PTrieCode.T_set b b table <= 2 * live_clock_atom p)%N. nia. }
    rewrite Nat2N.inj_add. nia.
  Qed.

  Lemma block_nodes_atom : forall p,
    (BC.T_nodes (R.prepare p) <=
      live_clock_atom p * N.of_nat (length (BC.nodes (R.prepare p)) + 1))%N.
  Proof.
    intro p. pose proof (BC.T_nodes_le (R.prepare p)) as Hnodes.
    assert (Hc : (BC.c_cfg_adj <= live_clock_scale)%N) by (unfold live_clock_scale; lia).
    pose proof (live_clock_scale_le_atom p) as Hatom. nia.
  Qed.

  Lemma group_point_atom : forall p x n rows,
    In n (C.nodes (R.prepare p)) ->
    (T_group_point (R.prepare p) (block_index (BC.nodes (R.prepare p))) x n rows <=
      16 * live_clock_atom p)%N.
  Proof.
    intros p x n rows Hn. set (q := R.prepare p).
    pose proof (live_clock_atom_positive p) as Hpositive.
    pose proof (block_lookup_atom p (SP.block_of_point q n)) as Hlookup.
    assert (Howner : (SP.T_block_of_point q n <= live_clock_atom p)%N).
    { eapply N.le_trans; [apply SP.T_block_of_point_le|]. apply live_clock_product;
        [unfold live_clock_scale; lia|now apply live_node_key]. }
    time_unfold T_group_point. fold q in Hn, Hlookup, Howner |- *.
    destruct (live_lookup (SP.block_of_point q n) (block_index (BC.nodes q))) as [b|]
      eqn:Hget; [|nia].
    rewrite live_lookup_correct in Hget.
    destruct (block_index_binding _ _ _ Hget) as [Hb Hkey].
    pose proof (live_block_key p b Hb) as Hblock.
    assert (Hparam : (SP.T_parameter_edge q b <= live_clock_atom p)%N).
    { eapply N.le_trans; [apply SP.T_parameter_edge_le|]. apply live_clock_product;
        [unfold live_clock_scale; lia|exact Hblock]. }
    pose proof (live_src_atom p (SP.parameter_edge q b)) as Hsrc.
    fold q in Hsrc.
    pose proof (live_eqb_node_atom p n (C.src q (SP.parameter_edge q b)) Hn) as Heqb.
    pose proof (live_row_atom _ p rows b Hblock) as Hrow.
    pose proof (live_set_atom _ p b (x :: index_row rows b) rows Hblock) as Hset.
    destruct (N.eqb n (C.src q (SP.parameter_edge q b))); nia.
  Qed.

  (** Every entry-cache value is a listed block, including on non-SSA inputs. *)
  Lemma entry_table_binding : forall q bs key b,
    trie_get key (entry_table q bs) = Some b -> In b bs.
  Proof.
    intros q bs key b Hget. unfold entry_table in Hget.
    destruct (entry_nodes_binding q (block_index bs) (C.nodes q) key b Hget)
      as [n [Hn [Hkey Hentry]]].
    unfold entry_block in Hentry.
    destruct (live_lookup (SP.block_of_point q n) (block_index bs)) as [target|]
      eqn:Hlookup; [|discriminate].
    destruct (N.eqb n (C.src q (SP.parameter_edge q target))); [|discriminate].
    injection Hentry as <-. rewrite live_lookup_correct in Hlookup.
    exact (proj1 (block_index_binding bs _ _ Hlookup)).
  Qed.

  (** Testing one listed point for block entry fits the primitive budget. *)
  Lemma entry_block_atom : forall p n, In n (C.nodes (R.prepare p)) ->
    (T_entry_block (R.prepare p) (block_index (BC.nodes (R.prepare p))) n <=
      8 * live_clock_atom p)%N.
  Proof.
    intros p n Hn. set (q := R.prepare p).
    pose proof (live_clock_atom_positive p) as Hpositive.
    pose proof (block_lookup_atom p (SP.block_of_point q n)) as Hlookup.
    assert (Howner : (SP.T_block_of_point q n <= live_clock_atom p)%N).
    { eapply N.le_trans; [apply SP.T_block_of_point_le|]. apply live_clock_product;
        [unfold live_clock_scale; lia|now apply live_node_key]. }
    time_unfold T_entry_block. fold q in Hn, Hlookup, Howner |- *.
    destruct (live_lookup (SP.block_of_point q n) (block_index (BC.nodes q))) as [b|]
      eqn:Hget; [|nia].
    rewrite live_lookup_correct in Hget.
    destruct (block_index_binding _ _ _ Hget) as [Hb Hkey].
    assert (Hparam : (SP.T_parameter_edge q b <= live_clock_atom p)%N).
    { eapply N.le_trans; [apply SP.T_parameter_edge_le|]. apply live_clock_product;
        [unfold live_clock_scale; lia|now apply live_block_key]. }
    pose proof (live_src_atom p (SP.parameter_edge q b)) as Hsrc.
    pose proof (live_eqb_node_atom p n (C.src q (SP.parameter_edge q b)) Hn) as Heqb.
    fold q in Hsrc. destruct (N.eqb n (C.src q (SP.parameter_edge q b))); nia.
  Qed.

  (** Caching one listed point pays for its test, encoding and insertion. *)
  Lemma entry_insert_atom : forall p n table, In n (C.nodes (R.prepare p)) ->
    (T_entry_insert (R.prepare p) (block_index (BC.nodes (R.prepare p))) n table <=
      16 * live_clock_atom p)%N.
  Proof.
    intros p n table Hn.
    pose proof (live_clock_atom_positive p) as Hpositive.
    pose proof (entry_block_atom p n Hn) as Hentry.
    pose proof (live_encode_node_atom p n Hn) as Hencode.
    pose proof (live_node_key p n Hn) as Hkey.
    time_unfold T_entry_insert.
    destruct (entry_block (R.prepare p) (block_index (BC.nodes (R.prepare p))) n)
      as [b|]; [|nia].
    pose proof (live_set_atom _ p (N.encode n) b table Hkey) as Hset. nia.
  Qed.

  (** Table preparation scans bounded points once and does not encode an unchecked endpoint. *)
  Lemma entry_table_atom : forall p,
    (T_entry_table (R.prepare p) (BC.nodes (R.prepare p)) <=
      4 * live_clock_atom p * N.of_nat (length (BC.nodes (R.prepare p)) + 1) +
      32 * live_clock_atom p * N.of_nat (length (C.nodes (R.prepare p)) + 1))%N.
  Proof.
    intro p. pose proof (live_clock_atom_positive p) as Hpositive.
    pose proof (block_index_atom p) as Hblocks.
    pose proof (live_nodes_atom p) as Hnodes.
    time_unfold T_entry_table. cbn beta zeta.
    let p := constr:(p) in match goal with
    | |- context [List.T_fold_right ?step ?clock Empty (C.nodes (R.prepare p))] =>
      assert (Hfold : (List.T_fold_right step clock Empty (C.nodes (R.prepare p)) <=
        (16 * live_clock_atom p + 1) * N.of_nat (length (C.nodes (R.prepare p))) + 1)%N)
    end.
    { apply live_fold_clock_uniform. intros n Hn table. now apply entry_insert_atom. }
    rewrite !Nat2N.inj_add in *. nia.
  Qed.

  (** Grouping a cached entry pays for one encoded lookup and one row update. *)
  Lemma group_entry_atom : forall p x n rows, In n (C.nodes (R.prepare p)) ->
    (T_group_entry (entry_table (R.prepare p) (BC.nodes (R.prepare p))) x n rows <=
      16 * live_clock_atom p)%N.
  Proof.
    intros p x n rows Hn.
    pose proof (live_clock_atom_positive p) as Hpositive.
    pose proof (live_node_key p n Hn) as Hkey.
    pose proof (live_encode_node_atom p n Hn) as Hencode.
    pose proof (live_get_atom _ p (N.encode n)
      (entry_table (R.prepare p) (BC.nodes (R.prepare p))) Hkey) as Hget.
    time_unfold T_group_entry.
    destruct (trie_get (N.encode n) (entry_table (R.prepare p) (BC.nodes (R.prepare p))))
      as [b|] eqn:Hentry; [|nia].
    pose proof (live_block_key p b
      (entry_table_binding (R.prepare p) (BC.nodes (R.prepare p)) _ b Hentry)) as Hblock.
    pose proof (live_row_atom _ p rows b Hblock) as Hrow.
    pose proof (live_set_atom _ p b (x :: index_row rows b) rows Hblock) as Hset. nia.
  Qed.

  Lemma group_search_atom : forall p x rows, In x (U.universe (R.prepare p)) ->
    (List.T_fold_right (group_entry (entry_table (R.prepare p) (BC.nodes (R.prepare p))) x)
      (fun n acc => T_group_entry (entry_table (R.prepare p) (BC.nodes (R.prepare p)))
        x n acc) rows
      (search (length (C.nodes (R.prepare p))) (R.prepare p)
        (seed_index (R.prepare p)) (reverse_kills (R.prepare p)) x) <=
      20 * live_clock_atom p * N.of_nat (variable_work p x + 1))%N.
  Proof.
    intros p x rows Hx.
    pose proof (live_clock_atom_positive p) as Hpositive.
    pose proof (live_search_charge p x Hx) as Hcharge.
    pose proof (search_spec (R.prepare p) x (proj2 (PB.prepared_wf p))) as [Hdup Hspec].
    eapply N.le_trans.
    - apply live_fold_clock_uniform with (bound := (16 * live_clock_atom p)%N).
      intros n Hn acc. apply group_entry_atom. exact (proj1 (proj1 (Hspec n) Hn)).
    - rewrite Nat2N.inj_add. nia.
  Qed.

  Lemma cached_group_search_atom : forall p x rows, In x (U.universe (R.prepare p)) ->
    (List.T_fold_right (group_entry (entry_table (R.prepare p) (BC.nodes (R.prepare p))) x)
      (fun n acc => T_group_entry (entry_table (R.prepare p) (BC.nodes (R.prepare p)))
        x n acc) rows
      (cached_search (length (C.nodes (R.prepare p)))
        (seed_index (R.prepare p)) (incoming_table (R.prepare p)) x) <=
      20 * live_clock_atom p * N.of_nat (variable_work p x + 1))%N.
  Proof.
    intros p x rows Hx.
    pose proof (live_clock_atom_positive p) as Hpositive.
    pose proof (cached_search_charge p x Hx) as Hcharge.
    eapply N.le_trans.
    - apply live_fold_clock_uniform with (bound := (16 * live_clock_atom p)%N).
      intros n Hn acc. apply group_entry_atom.
      exact (proj1 (cached_search_live (R.prepare p) x n (proj2 (PB.prepared_wf p)) Hn)).
    - rewrite Nat2N.inj_add. nia.
  Qed.

  Lemma live_rows_atom : forall p (rows : ptrie (list positive)),
    (ListDef.T_map (fun b => (b, index_row rows b))
      (fun b => 1 + T_index_row rows b)%N (BC.nodes (R.prepare p)) <=
      4 * live_clock_atom p * N.of_nat (length (BC.nodes (R.prepare p)) + 1))%N.
  Proof.
    intros p rows. pose proof (live_clock_atom_positive p) as Hpositive.
    eapply N.le_trans.
    - apply live_map_clock_uniform with (price := (2 * live_clock_atom p)%N).
      intros b Hb. pose proof (live_row_atom _ p rows b (live_block_key p b Hb)) as Hrow. nia.
    - rewrite Nat2N.inj_add, N.mul_add_distr_l, N.mul_1_r.
      apply N.add_le_mono; [apply N.mul_le_mono_r; lia|lia].
  Qed.

  Lemma live_width_le_atom : forall p, (live_clock_width p <= live_clock_atom p)%N.
  Proof.
    intro p. pose proof live_clock_scale_positive as Hscale.
    unfold live_clock_atom.
    rewrite <- (N.mul_1_l (live_clock_width p)) at 1.
    apply N.mul_le_mono_r. change (1 * 1 * 1 <=
      64 * live_clock_scale * live_clock_scale)%N.
    repeat apply N.mul_le_mono; lia.
  Qed.

  Lemma live_uses_total : forall p,
    (fold_right N.add 0%N (map (U.T_uses (R.prepare p)) (C.edges (R.prepare p))) <=
      live_clock_atom p * N.of_nat (length (C.edges (R.prepare p)) +
        length (flat_map (U.uses (R.prepare p)) (C.edges (R.prepare p)))))%N.
  Proof.
    intro p. rewrite <- live_fold_lengths. apply live_sum_weight.
    intros e He; now apply live_uses_atom.
  Qed.

  Lemma live_defs_total : forall p,
    (fold_right N.add 0%N (map (U.T_defs (R.prepare p)) (C.edges (R.prepare p))) <=
      live_clock_atom p * N.of_nat (length (C.edges (R.prepare p)) +
        length (flat_map (U.defs (R.prepare p)) (C.edges (R.prepare p)))))%N.
  Proof.
    intro p. rewrite <- live_fold_lengths. apply live_sum_weight.
    intros e He; now apply live_defs_atom.
  Qed.

  Lemma live_exits_total : forall p,
    (fold_right N.add 0%N (map (U.T_exits (R.prepare p)) (C.nodes (R.prepare p))) <=
      live_clock_atom p * N.of_nat (length (C.nodes (R.prepare p)) +
        length (flat_map (U.exits (R.prepare p)) (C.nodes (R.prepare p)))))%N.
  Proof.
    intro p. rewrite <- live_fold_lengths. apply live_sum_weight.
    intros n Hn; now apply live_exits_atom.
  Qed.

  Lemma live_universe_work_atom : forall p,
    (U.universe_work (R.prepare p) <=
      16 * live_clock_atom p * N.of_nat (live_graph_load (R.prepare p)))%N.
  Proof.
    intro p. set (q := R.prepare p).
    pose proof (live_clock_atom_positive p) as Hpositive.
    pose proof (live_nodes_atom p) as Hnodes.
    pose proof (live_edges_atom p) as Hedges.
    pose proof (live_uses_total p) as Huses.
    pose proof (live_defs_total p) as Hdefs.
    pose proof (live_exits_total p) as Hexits.
    pose proof (live_seed_count q) as Hseeds.
    pose proof (live_def_count q) as Hdefcount.
    assert (Hwidth : (N.of_nat (U.occurrence_width q + 1) <= live_clock_atom p)%N).
    { pose proof (PB.occurrence_width_le p) as Hwidth.
      fold q in Hwidth.
      pose proof (live_width_le_atom p) as Hatom. unfold live_clock_width in Hatom. lia. }
    assert (Henc : (fold_right N.add 0%N (map PosKeyT.T_encode (U.occurrences q)) <=
      live_clock_atom p * N.of_nat (length (U.occurrences q)))%N).
    { apply live_sum_uniform. intros x Hx. time_simpl. exact Hpositive. }
    assert (Hwidthpaid : (N.of_nat (length (C.edges q) + length (C.nodes q) +
      length (U.occurrences q) + 1) * N.of_nat (U.occurrence_width q + 1) <=
      live_clock_atom p * N.of_nat (length (C.edges q) + length (C.nodes q) +
        length (U.occurrences q) + 1))%N).
    { rewrite N.mul_comm. apply N.mul_le_mono_r. exact Hwidth. }
    assert (Hseedpaid : (live_clock_atom p * N.of_nat
      (length (flat_map (U.uses q) (C.edges q)) +
        length (flat_map (U.exits q) (C.nodes q))) <=
      live_clock_atom p * N.of_nat (length (U.occurrences q)))%N).
    { apply N.mul_le_mono_l. lia. }
    assert (Hdefpaid : (live_clock_atom p * N.of_nat
      (length (flat_map (U.defs q) (C.edges q))) <=
      live_clock_atom p * N.of_nat (length (U.occurrences q)))%N).
    { apply N.mul_le_mono_l. lia. }
    unfold U.universe_work. rewrite live_sum_pair.
    fold q in Hnodes, Hedges, Huses, Hdefs, Hexits |- *.
    unfold live_graph_load. rewrite !Nat2N.inj_add in *. nia.
  Qed.

  Lemma live_universe_atom : forall p,
    (U.T_universe (R.prepare p) <=
      16 * live_clock_atom p * live_clock_scale *
        N.of_nat (live_graph_load (R.prepare p)))%N.
  Proof.
    intro p. pose proof (U.T_universe_le (R.prepare p)) as Huniverse.
    pose proof (live_universe_work_atom p) as Hwork.
    assert (Hc : (U.c_vars <= live_clock_scale)%N) by (unfold live_clock_scale; lia). nia.
  Qed.

  Lemma live_prepare_atom : forall p,
    (R.T_prepare p <= live_clock_atom p * N.of_nat (function_size p + 1))%N.
  Proof.
    intro p. pose proof (R.T_prepare_le p) as Hprepare.
    assert (Hc : (R.c_prepare <= live_clock_scale)%N) by (unfold live_clock_scale; lia).
    pose proof live_clock_scale_positive as Hscale.
    assert (Hfactor : (R.c_prepare * N.of_nat (function_width p + 1) <=
      live_clock_atom p)%N).
    { apply live_clock_product; [exact Hc|]. fold (live_clock_width p).
      rewrite <- (N.mul_1_l (live_clock_width p)) at 1.
      apply N.mul_le_mono_r. exact Hscale. }
    eapply N.le_trans; [exact Hprepare|].
    replace (R.c_prepare * N.of_nat (function_size p + 1) *
      N.of_nat (function_width p + 1))%N with
      (R.c_prepare * N.of_nat (function_width p + 1) *
        N.of_nat (function_size p + 1))%N by ring.
    now apply N.mul_le_mono_r.
  Qed.

  Lemma live_blocks_size : forall p,
    length (BC.nodes (R.prepare p)) <= function_size p.
  Proof.
    intro p. pose proof (PB.block_nodes_le p) as Hnodes.
    assert (Hblocks : length (blocks _ _ _ p) <= function_size p).
    { unfold function_size. lia. }
    lia.
  Qed.

  Lemma live_entries_all_variables_atom : forall p,
    (List.T_fold_right
      (fun x acc => fold_right
        (group_entry (entry_table (R.prepare p) (BC.nodes (R.prepare p))) x) acc
        (search (length (C.nodes (R.prepare p))) (R.prepare p)
          (seed_index (R.prepare p)) (reverse_kills (R.prepare p)) x))
      (fun x acc => 1 +
        (T_search (length (C.nodes (R.prepare p))) (R.prepare p)
          (seed_index (R.prepare p)) (reverse_kills (R.prepare p)) x +
        List.T_fold_right (group_entry (entry_table (R.prepare p) (BC.nodes (R.prepare p))) x)
          (fun n rows => T_group_entry (entry_table (R.prepare p) (BC.nodes (R.prepare p)))
            x n rows) acc
          (search (length (C.nodes (R.prepare p))) (R.prepare p)
            (seed_index (R.prepare p)) (reverse_kills (R.prepare p)) x)))%N
      Empty (U.universe (R.prepare p)) <=
      (192 * live_clock_atom p + 1) *
        N.of_nat (live_size p + length (U.universe (R.prepare p))) + 1)%N.
  Proof.
    intro p. pose proof (live_clock_atom_positive p) as Hpositive.
    rewrite <- (live_size_partition p), <- live_sum_extra.
    apply live_fold_clock_weight; [intros; lia|]. intros x Hx rows.
    pose proof (search_atom p x Hx) as Hsearch.
    pose proof (group_search_atom p x rows Hx) as Hgroup.
    rewrite Nat2N.inj_add in *. nia.
  Qed.

  Lemma live_all_variables_atom : forall p,
    (List.T_fold_right
      (fun x acc => fold_right
        (group_entry (entry_table (R.prepare p) (BC.nodes (R.prepare p))) x) acc
        (cached_search (length (C.nodes (R.prepare p)))
          (seed_index (R.prepare p)) (incoming_table (R.prepare p)) x))
      (fun x acc => 1 +
        (T_cached_search (length (C.nodes (R.prepare p)))
          (seed_index (R.prepare p)) (incoming_table (R.prepare p)) x +
        List.T_fold_right (group_entry (entry_table (R.prepare p) (BC.nodes (R.prepare p))) x)
          (fun n rows => T_group_entry (entry_table (R.prepare p) (BC.nodes (R.prepare p)))
            x n rows) acc
          (cached_search (length (C.nodes (R.prepare p)))
            (seed_index (R.prepare p)) (incoming_table (R.prepare p)) x)))%N
      Empty (U.universe (R.prepare p)) <=
      (192 * live_clock_atom p + 1) *
        N.of_nat (live_size p + length (U.universe (R.prepare p))) + 1)%N.
  Proof.
    intro p. pose proof (live_clock_atom_positive p) as Hpositive.
    rewrite <- (live_size_partition p), <- live_sum_extra.
    apply live_fold_clock_weight; [intros; lia|]. intros x Hx rows.
    pose proof (cached_search_atom p x Hx) as Hsearch.
    pose proof (cached_group_search_atom p x rows Hx) as Hgroup.
    rewrite Nat2N.inj_add in *. nia.
  Qed.

  Lemma live_driver_atom : forall p,
    (T_live_in p <= 4096 * live_clock_atom p * live_clock_scale * live_clock_scale *
      N.of_nat (function_size p + live_size p + 1))%N.
  Proof.
    intro p. set (q := R.prepare p).
    pose proof live_clock_scale_positive as Hscale.
    pose proof (live_clock_atom_positive p) as Hpositive.
    pose proof (live_prepare_atom p) as Hprepare.
    pose proof (live_nodes_atom p) as Hnodes.
    pose proof (Datatypes.T_length_le (C.nodes q)) as Hlength.
    pose proof (seed_index_atom p) as Hseeds.
    pose proof (incoming_table_atom p) as Hkills.
    pose proof (block_nodes_atom p) as Hblocks.
    pose proof (entry_table_atom p) as Hlisted.
    pose proof (live_universe_atom p) as Huniverse.
    pose proof (live_all_variables_atom p) as Hvariables.
    pose proof (live_universe_length q) as Hvars.
    pose proof (live_blocks_size p) as Hblockcount.
    pose proof (live_graph_load_bound p) as Hload.
    time_unfold T_live_in. cbn beta zeta.
    fold q in Hnodes, Hlength, Hseeds, Hkills, Hblocks, Hlisted, Huniverse,
      Hvariables, Hvars, Hblockcount, Hload |- *.
    match goal with
    | |- context [ListDef.T_map (fun b => (b, index_row ?rows b)) _ _] =>
      pose proof (live_rows_atom p rows) as Hrows
    end.
    fold q in Hrows.
    assert (Hnodecount : (N.of_nat (length (C.nodes q) + 1) <=
      N.of_nat (live_graph_load q))%N) by (unfold live_graph_load; lia).
    assert (Hnodepaid : (live_clock_atom p * N.of_nat (length (C.nodes q) + 1) <=
      live_clock_atom p * N.of_nat (live_graph_load q))%N).
    { now apply N.mul_le_mono_l. }
    assert (Hunit : (N.of_nat (live_graph_load q) <=
      live_clock_atom p * N.of_nat (live_graph_load q))%N).
    { rewrite <- (N.mul_1_l (N.of_nat (live_graph_load q))) at 1.
      now apply N.mul_le_mono_r. }
    assert (Hstart : (1 <= live_clock_atom p * N.of_nat (live_graph_load q))%N).
    { eapply N.le_trans; [|exact Hunit]. unfold live_graph_load; lia. }
    assert (Hlift : (live_clock_atom p * N.of_nat (live_graph_load q) <=
      live_clock_atom p * live_clock_scale * N.of_nat (live_graph_load q))%N).
    { apply N.mul_le_mono_r. rewrite <- (N.mul_1_r (live_clock_atom p)) at 1.
      now apply N.mul_le_mono_l. }
    assert (Hblockpaid : (live_clock_atom p * N.of_nat (length (BC.nodes q) + 1) <=
      live_clock_atom p * N.of_nat (function_size p + 1))%N).
    { apply N.mul_le_mono_l. lia. }
    assert (Hvarfactor : ((192 * live_clock_atom p + 1) *
      N.of_nat (live_size p + length (U.universe q)) <=
      193 * live_clock_atom p * N.of_nat (live_size p + length (U.universe q)))%N).
    { apply N.mul_le_mono_r. lia. }
    assert (Hvariablepaid : (193 * live_clock_atom p *
      N.of_nat (live_size p + length (U.universe q)) <=
      193 * live_clock_atom p * N.of_nat (live_size p) +
      193 * live_clock_atom p * N.of_nat (live_graph_load q))%N).
    { rewrite Nat2N.inj_add, N.mul_add_distr_l. apply N.add_le_mono_l.
      apply N.mul_le_mono_l. unfold live_graph_load. lia. }
    assert (Hlocal : (T_live_in p <=
      1024 * live_clock_atom p * live_clock_scale * N.of_nat (live_graph_load q) +
      16 * live_clock_atom p * N.of_nat (function_size p + 1) +
      256 * live_clock_atom p * N.of_nat (live_size p))%N).
    { time_unfold T_live_in. cbn beta zeta. fold q.
      set (graph_budget := (live_clock_atom p * live_clock_scale *
        N.of_nat (live_graph_load q))%N).
      set (syntax_budget := (live_clock_atom p * N.of_nat (function_size p + 1))%N).
      set (live_budget := (live_clock_atom p * N.of_nat (live_size p))%N).
      assert (Hgraphscale : forall k, (k * live_clock_atom p *
        N.of_nat (live_graph_load q) <= k * graph_budget)%N).
      { intro k. replace (k * live_clock_atom p * N.of_nat (live_graph_load q))%N
          with (k * (live_clock_atom p * N.of_nat (live_graph_load q)))%N by ring.
        now apply N.mul_le_mono_l. }
      assert (Hblockscale : forall k, (k * live_clock_atom p *
        N.of_nat (length (BC.nodes q) + 1) <= k * syntax_budget)%N).
      { intro k. replace (k * live_clock_atom p * N.of_nat (length (BC.nodes q) + 1))%N
          with (k * (live_clock_atom p * N.of_nat (length (BC.nodes q) + 1)))%N by ring.
        now apply N.mul_le_mono_l. }
      assert (Hprepare_budget : (R.T_prepare p <= syntax_budget)%N) by exact Hprepare.
      assert (Hnode_budget : (C.T_nodes q <= graph_budget)%N).
      { eapply N.le_trans; [exact Hnodes|].
        eapply N.le_trans; [exact Hnodepaid|exact Hlift]. }
      assert (Hlength_budget : (Datatypes.T_length (C.nodes q) <= graph_budget)%N).
      { eapply N.le_trans; [exact Hlength|].
        eapply N.le_trans; [|exact Hlift].
        eapply N.le_trans; [|exact Hunit].
        change (N.of_nat (length (C.nodes q)) + N.of_nat 1 <=
          N.of_nat (live_graph_load q))%N.
        rewrite <- Nat2N.inj_add. exact Hnodecount. }
      pose proof (N.le_trans _ _ _ Hseeds (Hgraphscale 256%N)) as Hseed_budget.
      pose proof (N.le_trans _ _ _ Hkills (Hgraphscale 128%N)) as Hkill_budget.
      assert (Hblocks_budget : (BC.T_nodes q <= syntax_budget)%N).
      { eapply N.le_trans; [exact Hblocks|exact Hblockpaid]. }
      assert (Hlisted_budget : (T_entry_table q (BC.nodes q) <=
        4 * syntax_budget + 32 * graph_budget)%N).
      { eapply N.le_trans; [exact Hlisted|]. apply N.add_le_mono.
        - apply Hblockscale.
        - replace (32 * live_clock_atom p * N.of_nat (length (C.nodes q) + 1))%N
            with (32 * (live_clock_atom p *
              N.of_nat (length (C.nodes q) + 1)))%N by ring.
          apply N.mul_le_mono_l. eapply N.le_trans; [exact Hnodepaid|exact Hlift]. }
      pose proof (N.le_trans _ _ _ Hrows (Hblockscale 4%N)) as Hrows_budget.
      assert (Huniverse_budget : (U.T_universe q <= 16 * graph_budget)%N).
      { eapply N.le_trans; [exact Huniverse|]. unfold graph_budget. ring_simplify.
        apply N.le_refl. }
      assert (Hvs : ((192 * live_clock_atom p + 1) *
        N.of_nat (live_size p + length (U.universe q)) + 1 <=
        193 * live_budget + 193 * graph_budget + 1)%N).
      { apply N.add_le_mono_r. eapply N.le_trans; [exact Hvarfactor|].
        eapply N.le_trans; [exact Hvariablepaid|].
        replace (193 * live_clock_atom p * N.of_nat (live_size p))%N with
          (193 * live_budget)%N by (unfold live_budget; ring).
        apply N.add_le_mono_l. apply Hgraphscale. }
      pose proof (N.le_trans _ _ _ Hvariables Hvs) as Hvars_budget.
      assert (Hstart_budget : (1 <= graph_budget)%N).
      { eapply N.le_trans; [exact Hstart|exact Hlift]. }
      replace (1024 * live_clock_atom p * live_clock_scale *
        N.of_nat (live_graph_load q) + 16 * live_clock_atom p *
        N.of_nat (function_size p + 1) + 256 * live_clock_atom p *
        N.of_nat (live_size p))%N with
        (1024 * graph_budget + 16 * syntax_budget + 256 * live_budget)%N by
          (unfold graph_budget, syntax_budget, live_budget; ring).
      clearbody graph_budget syntax_budget live_budget.
      clear - p q graph_budget syntax_budget live_budget Hprepare_budget Hnode_budget
        Hlength_budget Hseed_budget Hkill_budget Hblocks_budget Hlisted_budget
        Huniverse_budget Hvars_budget Hrows_budget Hstart_budget.
      lia. }
    assert (Hloadpaid : (live_clock_atom p * live_clock_scale *
      N.of_nat (live_graph_load q) <= 2 * live_clock_atom p * live_clock_scale *
      live_clock_scale * N.of_nat (function_size p + 1))%N).
    { replace (2 * live_clock_atom p * live_clock_scale * live_clock_scale *
        N.of_nat (function_size p + 1))%N with
        (live_clock_atom p * live_clock_scale *
          (2 * live_clock_scale * N.of_nat (function_size p + 1)))%N by ring.
      now apply N.mul_le_mono_l. }
    assert (Hraise : (live_clock_atom p <=
      live_clock_atom p * live_clock_scale * live_clock_scale)%N).
    { rewrite <- (N.mul_1_r (live_clock_atom p)) at 1.
      rewrite <- (N.mul_1_r (live_clock_atom p * 1)) at 1.
      repeat apply N.mul_le_mono; lia. }
    assert (Hsyntaxpaid : (live_clock_atom p * N.of_nat (function_size p + 1) <=
      live_clock_atom p * live_clock_scale * live_clock_scale *
        N.of_nat (function_size p + 1))%N) by now apply N.mul_le_mono_r.
    assert (Hlivepaid : (live_clock_atom p * N.of_nat (live_size p) <=
      live_clock_atom p * live_clock_scale * live_clock_scale *
        N.of_nat (live_size p))%N) by now apply N.mul_le_mono_r.
    assert (Hfirst : (1024 * live_clock_atom p * live_clock_scale *
      N.of_nat (live_graph_load q) <= 2048 * live_clock_atom p * live_clock_scale *
      live_clock_scale * N.of_nat (function_size p + 1))%N).
    { replace (1024 * live_clock_atom p * live_clock_scale *
        N.of_nat (live_graph_load q))%N with
        (1024 * (live_clock_atom p * live_clock_scale *
          N.of_nat (live_graph_load q)))%N by ring.
      replace (2048 * live_clock_atom p * live_clock_scale * live_clock_scale *
        N.of_nat (function_size p + 1))%N with
        (1024 * (2 * live_clock_atom p * live_clock_scale * live_clock_scale *
          N.of_nat (function_size p + 1)))%N by ring.
      now apply N.mul_le_mono_l. }
    assert (Hsecond : (16 * live_clock_atom p * N.of_nat (function_size p + 1) <=
      16 * live_clock_atom p * live_clock_scale * live_clock_scale *
        N.of_nat (function_size p + 1))%N).
    { replace (16 * live_clock_atom p * N.of_nat (function_size p + 1))%N with
        (16 * (live_clock_atom p * N.of_nat (function_size p + 1)))%N by ring.
      replace (16 * live_clock_atom p * live_clock_scale * live_clock_scale *
        N.of_nat (function_size p + 1))%N with
        (16 * (live_clock_atom p * live_clock_scale * live_clock_scale *
          N.of_nat (function_size p + 1)))%N by ring.
      now apply N.mul_le_mono_l. }
    assert (Hthird : (256 * live_clock_atom p * N.of_nat (live_size p) <=
      256 * live_clock_atom p * live_clock_scale * live_clock_scale *
        N.of_nat (live_size p))%N).
    { replace (256 * live_clock_atom p * N.of_nat (live_size p))%N with
        (256 * (live_clock_atom p * N.of_nat (live_size p)))%N by ring.
      replace (256 * live_clock_atom p * live_clock_scale * live_clock_scale *
        N.of_nat (live_size p))%N with
        (256 * (live_clock_atom p * live_clock_scale * live_clock_scale *
          N.of_nat (live_size p)))%N by ring.
      now apply N.mul_le_mono_l. }
    eapply N.le_trans; [exact Hlocal|]. eapply N.le_trans.
    - apply N.add_le_mono; [apply N.add_le_mono; [exact Hfirst|exact Hsecond]|exact Hthird].
    - replace (2048 * live_clock_atom p * live_clock_scale * live_clock_scale *
        N.of_nat (function_size p + 1) + 16 * live_clock_atom p * live_clock_scale *
        live_clock_scale * N.of_nat (function_size p + 1) +
        256 * live_clock_atom p * live_clock_scale * live_clock_scale *
        N.of_nat (live_size p))%N with
        (live_clock_atom p * live_clock_scale * live_clock_scale *
          (2064 * N.of_nat (function_size p + 1) + 256 * N.of_nat (live_size p)))%N by ring.
      replace (4096 * live_clock_atom p * live_clock_scale * live_clock_scale *
        N.of_nat (function_size p + live_size p + 1))%N with
        (live_clock_atom p * live_clock_scale * live_clock_scale *
          (4096 * N.of_nat (function_size p + live_size p + 1)))%N by ring.
      apply N.mul_le_mono_l. rewrite !Nat2N.inj_add. lia.
  Qed.

  Lemma live_driver_bound : forall p,
    (T_live_in p <= live_driver_budget * N.of_nat (function_size p + live_size p + 1) *
      N.of_nat (function_width p + 1))%N.
  Proof.
    intro p. pose proof (live_driver_atom p) as Hdriver.
    unfold live_clock_atom, live_clock_width, live_driver_budget in *. nia.
  Qed.

  Lemma live_driver_complexity :
    T_live_in p ∈ 𝑂(N.of_nat ((function_size p + live_size p + 1) * (function_width p + 1)))
      for p.
  Proof.
    exists live_driver_budget. intros p Htrue. pose proof (live_driver_bound p) as Hclock.
    rewrite Nat2N.inj_mul. nia.
  Qed.

  Lemma live_rows_bound : forall p,
    (T_live_in p <= R.T_prepare p +
      live_driver_budget * N.of_nat (function_size p + live_size p + 1) *
        N.of_nat (function_width p + 1) + T_use_index (R.prepare p) +
      T_kill_index (R.prepare p) +
      fold_right N.add 0%N
        (map (T_explore (R.prepare p) (use_index (R.prepare p)) (kill_index (R.prepare p)))
          (U.universe (R.prepare p))))%N.
  Proof.
    intro p. pose proof (live_driver_bound p) as Hclock. lia.
  Qed.

  (** Path exploration pays for syntax and live predecessor incidences. *)
  Lemma T_live_in_le : forall p,
    (T_live_in p <= c_live * N.of_nat (function_size p + live_size p + 1) *
      N.of_nat (function_width p + 1))%N.
  Proof.
    exact live_driver_bound.
  Qed.
  (** The producer has the published output-sensitive bit-cost bound. *)
  Lemma live_in_complexity :
    T_live_in p ∈ 𝑂(N.of_nat ((function_size p + live_size p + 1) * (function_width p + 1)))
      for p.
  Proof.
    exact live_driver_complexity.
  Qed.
  (** Indexing reads each variable occurrence once at the syntax width. *)
  Lemma T_use_index_le : forall p,
    (T_use_index (R.prepare p) <= k_index * N.of_nat (function_size p + 1) *
      N.of_nat (function_width p + 1))%N.
  Proof.
    exact use_index_bound.
  Qed.
  (** The kill index reads each definition occurrence once at the syntax width. *)
  Lemma T_kill_index_le : forall p,
    (T_kill_index (R.prepare p) <= k_index * N.of_nat (function_size p + 1) *
      N.of_nat (function_width p + 1))%N.
  Proof.
    exact kill_index_bound.
  Qed.
  (** The driver prepares once, builds both indexes, searches each variable and groups
      rows. *)
  Lemma T_live_in_split : forall p,
    (T_live_in p <= R.T_prepare p +
      k_rows * N.of_nat (function_size p + live_size p + 1) *
        N.of_nat (function_width p + 1) + T_use_index (R.prepare p) +
      T_kill_index (R.prepare p) +
      fold_right N.add 0%N
        (map (T_explore (R.prepare p) (use_index (R.prepare p)) (kill_index (R.prepare p)))
          (U.universe (R.prepare p))))%N.
  Proof.
    (* The independent driver bound covers this allowance; the separate plan clocks
       are nonnegative. LiveCode traverses the grouped reverse index. *)
    exact live_rows_bound.
  Qed.

  (** Emitted rows name listed blocks and variables of the universe. *)
  Lemma live_in_ids : forall p row, In row (live_in p) ->
    In (fst row) (BC.nodes (R.prepare p)) /\ incl (snd row) (U.universe (R.prepare p)).
  Proof.
    intros p row Hin. unfold live_in in Hin. apply in_map_iff in Hin.
    destruct Hin as [b [<- Hb]]. split; [exact Hb|]. cbn.
    apply group_entry_variables_values.
  Qed.
End LiveT.
