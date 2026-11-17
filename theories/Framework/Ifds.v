(** * Balanced IFDS path-edge constraints

    Finite rules combine caller and callee path edges at matched returns.
    For example, an internal edge propagates one fact without changing stack level.
    Builds on: Framework.IfdsSig and Fixpoint.Query. *)

From Stdlib Require Import List Bool NArith PArith Arith Lia.
From Argent Require Import Time Tactics Std Loop BigO.
From Galois.Base Require Import KeySig Code Trie.
From Galois.Lattice Require Import LatticeSig.
From Galois.Fixpoint Require Import Query SystemSig.
From Galois.Program Require Import CfgSig IcfgSig.
From Galois.Framework Require Import IfdsSig.

(** Enumerate finite rules with binary occurrence identifiers. *)
Fixpoint path_number {N E F} (next : positive) (rules : list (path_rule N E F))
    : list (path_row N E F) :=
  match rules with
  | nil => nil
  | r :: rest => PathRow next r :: path_number (Pos.succ next) rest
  end.
TimeFun path_number.

(** Numbering preserves the rule inventory and its occurrence order. *)
Lemma path_number_rules {N E F} : forall next (rules : list (path_rule N E F)),
  map path_row_rule (path_number next rules) = rules.
Proof.
  intros next rules; revert next.
  induction rules as [|rule rules IH]; intro next; cbn [path_number map].
  - reflexivity.
  - now rewrite IH.
Qed.

(** Numbering allocates one row per rule occurrence. *)
Lemma path_number_length {N E F} : forall next (rules : list (path_rule N E F)),
  length (path_number next rules) = length rules.
Proof.
  intros next rules.
  rewrite <- (length_map path_row_rule (path_number next rules)), path_number_rules.
  reflexivity.
Qed.

(** Set digits pay for carries when the next row identifier is incremented. *)
Fixpoint path_number_potential (next : positive) : N :=
  match next with
  | xI rest => (path_number_potential rest + 1)%N
  | xO rest => path_number_potential rest
  | xH => 1%N
  end.

(** Each successor consumes at most two units after accounting for its changed digits. *)
Lemma path_number_carry : forall next,
  (Pos.T_succ next + path_number_potential (Pos.succ next) <=
    path_number_potential next + 2)%N.
Proof.
  induction next as [next IH|next IH|]; time_step.
Qed.

(** Binary numbering is linear in the number of rows plus the initial digit potential. *)
Lemma T_path_number_le {N E F} : forall next (rules : list (path_rule N E F)),
  (T_path_number next rules <=
    3 * N.of_nat (length rules) + path_number_potential next + 1)%N.
Proof.
  intros next rules; revert next.
  induction rules as [|rule rules IH]; intro next.
  - time_step.
  - pose proof (path_number_carry next) as Hcarry.
    pose proof (IH (Pos.succ next)) as Hrest.
    time_step.
Qed.

(** Rule numbering is linear in its output count and initial binary carry potential. *)
Lemma path_number_bigO {N E F} :
  bigO (X := positive * list (path_rule N E F)) (fun _ => True)
    (fun '(next, rules) => (N.of_nat (length rules) + path_number_potential next)%N)
    (fun '(next, rules) => T_path_number next rules).
Proof.
  apply bigO_intro with (c := 3%N).
  intros [next rules] _.
  pose proof (T_path_number_le next rules) as Htime.
  change (T_path_number next rules <=
    3 * (N.of_nat (length rules) + path_number_potential next) + 3)%N; nia.
Qed.

(** Propagating an empty collection of facts keeps it empty. *)
Lemma path_fold_nil {E F} (flow : E -> F -> list F) : forall path,
  fold_left (fun facts e => flat_map (flow e) facts) path nil = nil.
Proof.
  induction path as [|e path IH]; cbn [fold_left flat_map]; assumption || reflexivity.
Qed.

(** Independent input collections propagate independently along the same path. *)
Lemma path_fold_app {E F} (flow : E -> F -> list F) : forall path left right,
  fold_left (fun facts e => flat_map (flow e) facts) path (left ++ right) =
    fold_left (fun facts e => flat_map (flow e) facts) path left ++
    fold_left (fun facts e => flat_map (flow e) facts) path right.
Proof.
  induction path as [|e path IH]; intros left right; cbn [fold_left].
  - reflexivity.
  - rewrite flat_map_app; apply IH.
Qed.

(** Propagation from a list is the concatenation of its singleton propagations. *)
Lemma path_fold_facts {E F} (flow : E -> F -> list F) : forall path facts,
  fold_left (fun facts e => flat_map (flow e) facts) path facts =
    flat_map (fun d => path_facts flow d path) facts.
Proof.
  intros path facts; induction facts as [|d facts IH].
  - apply path_fold_nil.
  - change (fold_left (fun facts e => flat_map (flow e) facts)
      path ((d :: nil) ++ facts) =
      path_facts flow d path ++ flat_map (fun x => path_facts flow x path) facts).
    rewrite path_fold_app, IH; reflexivity.
Qed.

(** Concatenating paths composes their fact relations in occurrence order. *)
Lemma path_facts_app {E F} (flow : E -> F -> list F) : forall d left right,
  path_facts flow d (left ++ right) =
    flat_map (fun x => path_facts flow x right) (path_facts flow d left).
Proof.
  intros d left right; unfold path_facts at 1.
  rewrite fold_left_app, path_fold_facts; reflexivity.
Qed.

(** A one-edge path has exactly the edge's flow results. *)
Lemma path_facts_single {E F} (flow : E -> F -> list F) : forall d e,
  path_facts flow d (e :: nil) = flow e d.
Proof.
  intros d e; unfold path_facts; cbn [fold_left flat_map]; apply app_nil_r.
Qed.

(** The first edge chooses the input fact of the remaining path. *)
Lemma path_facts_cons {E F} (flow : E -> F -> list F) : forall d e path,
  path_facts flow d (e :: path) =
    flat_map (fun x => path_facts flow x path) (flow e d).
Proof.
  intros d e path.
  change (path_facts flow d ((e :: nil) ++ path) =
    flat_map (fun x => path_facts flow x path) (flow e d)).
  rewrite path_facts_app, path_facts_single; reflexivity.
Qed.

(** Rule enumeration retains seed, internal and matched-call occurrences. *)
Definition path_rules {N E F Site} (site_eqb : Site -> Site -> bool)
    (kind : E -> edge_kind Site) (dst : E -> N) (facts : list F)
    (flow : E -> F -> list F) (seeds : list (N * F)) (edges : list E)
    : list (path_rule N E F) :=
  map (fun nd => PathIdentity (fst nd) (snd nd)) seeds ++
  flat_map (fun e => match kind e with
    | Call _ => flat_map (fun x => map (fun d => PathIdentity (dst e) d) (flow e x)) facts
    | _ => nil
    end) edges ++
  flat_map (fun d0 => flat_map (fun e => match kind e with
    | Intra | CallToReturn _ => flat_map
        (fun x => map (fun y => PathStep d0 e x y) (flow e x)) facts
    | _ => nil
    end) edges) facts ++
  flat_map (fun d0 => flat_map (fun call => match kind call with
    | Call site => flat_map (fun ret => match kind ret with
      | Return site' => if site_eqb site site' then
          flat_map (fun x => flat_map (fun a => flat_map (fun b =>
            map (fun y => PathReturn d0 call ret x a b y) (flow ret b)) facts)
            (flow call x)) facts
        else nil
      | _ => nil
      end) edges
    | _ => nil
    end) edges) facts.
TimeFun path_rules.

(** Cache an edge's fact pairs in their original input and output order. *)
Definition edge_pairs {E F} (flow : E -> F -> list F) (facts : list F) (e : E)
    : list (F * F) :=
  flat_map (fun x => map (fun y => (x, y)) (flow e x)) facts.
TimeFun edge_pairs.

(** Mapping cached pairs is the original nested mapping over flow results. *)
Lemma edge_pairs_step {E F A} (flow : E -> F -> list F) facts e (f : F -> F -> A) :
  map (fun '(x, y) => f x y) (edge_pairs flow facts e) =
    flat_map (fun x => map (f x) (flow e x)) facts.
Proof.
  unfold edge_pairs. induction facts as [|x facts IH]; cbn [flat_map map].
  - reflexivity.
  - rewrite map_app, map_map, IH. reflexivity.
Qed.

(** Projecting cached outputs preserves the concatenated flow results. *)
Lemma edge_pairs_snd {E F} (flow : E -> F -> list F) facts e :
  map snd (edge_pairs flow facts e) = flat_map (flow e) facts.
Proof.
  change (map (fun '(x, y) => (fun _ y => y) x y)
    (edge_pairs flow facts e) = flat_map (flow e) facts).
  rewrite edge_pairs_step. apply flat_map_ext. intro x. apply map_id.
Qed.

(** Flattening a mapped list composes the two callbacks. *)
Local Lemma path_flat_map_map {A B C} (f : B -> list C) (g : A -> B) xs :
  flat_map f (map g xs) = flat_map (fun x => f (g x)) xs.
Proof.
  induction xs as [|x xs IH]; cbn [map flat_map].
  - reflexivity.
  - now rewrite IH.
Qed.

(** Flat-mapping cached pairs preserves both nested occurrence orders. *)
Lemma edge_pairs_flat_map {E F A} (flow : E -> F -> list F) facts e
    (f : F -> F -> list A) :
  flat_map (fun '(x, y) => f x y) (edge_pairs flow facts e) =
    flat_map (fun x => flat_map (f x) (flow e x)) facts.
Proof.
  unfold edge_pairs. induction facts as [|x facts IH]; cbn [flat_map].
  - reflexivity.
  - rewrite flat_map_app, path_flat_map_map, IH. reflexivity.
Qed.

(** An edge cache stores its classification and ordered fact pairs without callbacks. *)
Record path_edge_info (E F Site : Type) := PathEdgeInfo {
  info_edge : E;
  info_kind : edge_kind Site;
  info_pairs : list (F * F)
}.
Arguments PathEdgeInfo {E F Site}.
Arguments info_edge {E F Site}.
Arguments info_kind {E F Site}.
Arguments info_pairs {E F Site}.
TimeFun info_edge.
TimeFun info_kind.
TimeFun info_pairs.

(** A missing site has no return edges. *)
Definition return_rows {E F Site} (code : positive)
    (index : ptrie (list (path_edge_info E F Site))) : list (path_edge_info E F Site) :=
  match trie_get code index with
  | Some rows => rows
  | None => nil
  end.
TimeFun return_rows.

(** Folding from the right preserves the source order of returns at every site. *)
Definition return_index {E F Site} (site_code : Site -> positive)
    (infos : list (path_edge_info E F Site)) : ptrie (list (path_edge_info E F Site)) :=
  fold_right (fun i acc => match info_kind i with
    | Return s =>
      let code := site_code s in
      PTrieCode.set code (i :: return_rows code acc) acc
    | _ => acc
    end) Empty infos.
TimeFun return_index.

(** Looking up a site selects exactly its return occurrences in source order. *)
Lemma return_index_spec {E F Site} (site_code : Site -> positive)
    (infos : list (path_edge_info E F Site)) code :
  return_rows code (return_index site_code infos) =
    filter (fun i => match info_kind i with
      | Return s => Pos.eqb code (site_code s)
      | _ => false
      end) infos.
Proof.
  induction infos as [|i infos IH].
  - unfold return_index, return_rows; cbn [fold_right filter].
    rewrite PTrie.get_empty. reflexivity.
  - cbn [return_index fold_right filter].
    destruct (info_kind i) as [|site|site|site]; try exact IH.
    destruct (Pos.eqb code (site_code site)) eqn:Hsame.
    + apply Pos.eqb_eq in Hsame. subst code. unfold return_rows at 1.
      rewrite PTrie.get_set_same. exact (f_equal (cons i) IH).
    + apply Pos.eqb_neq in Hsame. unfold return_rows at 1.
      rewrite PTrie.get_set_other by exact Hsame. exact IH.
Qed.

(** Resolve each call's return bucket once, outside the initial-fact traversal. *)
Definition path_calls {E F Site} (site_code : Site -> positive)
    (returns : ptrie (list (path_edge_info E F Site)))
    (infos : list (path_edge_info E F Site))
    : list (path_edge_info E F Site * list (path_edge_info E F Site)) :=
  flat_map (fun call => match info_kind call with
    | Call site => (call, return_rows (site_code site) returns) :: nil
    | _ => nil
    end) infos.
TimeFun path_calls.

(** Traversing cached calls agrees with selecting calls from the edge inventory. *)
Local Lemma path_calls_flat_map {E F Site A} (site_code : Site -> positive) returns infos
    (f : path_edge_info E F Site * list (path_edge_info E F Site) -> list A) :
  flat_map f (path_calls site_code returns infos) =
    flat_map (fun call => match info_kind call with
      | Call site => f (call, return_rows (site_code site) returns)
      | _ => nil
      end) infos.
Proof.
  unfold path_calls. induction infos as [|i infos IH]; cbn [flat_map].
  - reflexivity.
  - destruct (info_kind i); cbn [flat_map fst snd app];
      try exact IH; now rewrite IH.
Qed.

(** Hoist edge callbacks and use an ordered site index for matched returns. *)
Definition path_rules_fast {N E F Site} (site_code : Site -> positive)
    (kind : E -> edge_kind Site) (dst : E -> N) (facts : list F)
    (flow : E -> F -> list F) (seeds : list (N * F)) (edges : list E)
    : list (path_rule N E F) :=
  let infos := map (fun e => PathEdgeInfo e (kind e) (edge_pairs flow facts e)) edges in
  let returns := return_index site_code infos in
  let calls := path_calls site_code returns infos in
  map (fun '(n, d) => PathIdentity n d) seeds ++
  flat_map (fun i =>
    match i with
    | PathEdgeInfo e k pairs =>
      match k with
      | Call _ =>
        let target := dst e in
        map (fun '(_, y) => PathIdentity target y) pairs
      | _ => nil
      end
    end) infos ++
  flat_map (fun d0 => flat_map (fun i =>
    match i with
    | PathEdgeInfo e k pairs =>
      match k with
      | Intra | CallToReturn _ => map (fun '(x, y) => PathStep d0 e x y) pairs
      | _ => nil
      end
    end) infos) facts ++
  flat_map (fun d0 => flat_map (fun '(call, rets) =>
    match call with
    | PathEdgeInfo call_edge _ call_pairs =>
      flat_map (fun ret =>
        match ret with
        | PathEdgeInfo ret_edge _ ret_pairs =>
          flat_map (fun '(x, a) => map (fun '(b, y) =>
            PathReturn d0 call_edge ret_edge x a b y) ret_pairs) call_pairs
        end) rets
    end) calls) facts.
TimeFun path_rules_fast.

(** Filtering before flattening is equivalent to skipping the rejected occurrences. *)
Local Lemma path_flat_map_filter {A B} (f : A -> list B) keep xs :
  flat_map f (filter keep xs) = flat_map (fun x => if keep x then f x else nil) xs.
Proof.
  induction xs as [|x xs IH]; cbn [filter flat_map].
  - reflexivity.
  - destruct (keep x); cbn [flat_map]; now rewrite IH.
Qed.

(** Cached call and return pairs preserve the original nested fact traversal. *)
Local Lemma path_return_pairs {N E F} (flow : E -> F -> list F) facts d0 call ret :
  flat_map (fun '(x, a) => map (fun '(b, y) =>
    @PathReturn N E F d0 call ret x a b y)
    (edge_pairs flow facts ret)) (edge_pairs flow facts call) =
  flat_map (fun x => flat_map (fun a => flat_map (fun b =>
    map (fun y => PathReturn d0 call ret x a b y) (flow ret b)) facts)
    (flow call x)) facts.
Proof.
  rewrite (edge_pairs_flat_map flow facts call (fun x a =>
    map (fun '(b, y) => @PathReturn N E F d0 call ret x a b y)
      (edge_pairs flow facts ret))).
  apply flat_map_ext. intro x.
  apply flat_map_ext. intro a. apply edge_pairs_step.
Qed.

(** The indexed builder preserves every rule occurrence and its exact order. *)
Theorem path_rules_fast_agrees {N E F Site} (site_eqb : Site -> Site -> bool)
    (site_code : Site -> positive) (kind : E -> edge_kind Site) (dst : E -> N)
    (facts : list F) (flow : E -> F -> list F) (seeds : list (N * F)) (edges : list E) :
  (forall s s', site_eqb s s' = Pos.eqb (site_code s) (site_code s')) ->
  path_rules_fast site_code kind dst facts flow seeds edges =
    path_rules site_eqb kind dst facts flow seeds edges.
Proof.
  intro Hcode. unfold path_rules_fast, path_rules.
  apply f_equal2; [apply map_ext; intros [n d]; reflexivity|]. apply f_equal2.
  - rewrite path_flat_map_map. apply flat_map_ext. intro e.
    cbn [info_kind info_edge info_pairs]. destruct (kind e); try reflexivity.
    exact (edge_pairs_step flow facts e (fun _ d => @PathIdentity N E F (dst e) d)).
  - apply f_equal2.
    + apply flat_map_ext. intro d0. rewrite path_flat_map_map.
      apply flat_map_ext. intro e. cbn [info_kind info_edge info_pairs].
      destruct (kind e); try reflexivity; apply edge_pairs_step.
    + apply flat_map_ext. intro d0. rewrite path_calls_flat_map, path_flat_map_map.
      apply flat_map_ext. intro call. cbn [info_kind info_edge info_pairs].
      destruct (kind call) as [|site|site|site]; try reflexivity.
      cbn [fst snd info_edge info_pairs].
      rewrite return_index_spec, path_flat_map_filter, path_flat_map_map.
      apply flat_map_ext. intro ret. cbn [info_kind info_edge info_pairs].
      destruct (kind ret) as [|ret_site|ret_site|ret_site]; try reflexivity.
      rewrite Hcode. destruct (Pos.eqb (site_code site) (site_code ret_site));
        [apply path_return_pairs|reflexivity].
Qed.

(** Sum a nonnegative structural charge over input occurrences. *)
Fixpoint path_weight {A} (charge : A -> N) (xs : list A) : N :=
  match xs with
  | nil => 0%N
  | x :: rest => (charge x + path_weight charge rest)%N
  end.


Local Lemma path_weight_le {A} (f g : A -> N) xs :
  (forall x, In x xs -> (f x <= g x)%N) -> (path_weight f xs <= path_weight g xs)%N.
Proof.
  induction xs as [|x xs IH]; intro Hfg; cbn [path_weight fold_right].
  - reflexivity.
  - pose proof (Hfg x (or_introl eq_refl)) as Hhead.
    specialize (IH (fun y Hy => Hfg y (or_intror Hy))); nia.
Qed.

Local Lemma path_weight_add {A} (f g : A -> N) xs :
  path_weight (fun x => f x + g x)%N xs = (path_weight f xs + path_weight g xs)%N.
Proof.
  induction xs as [|x xs IH]; cbn [path_weight fold_right] in *; nia.
Qed.

Local Lemma path_weight_scale {A} k (f : A -> N) xs :
  path_weight (fun x => k * f x)%N xs = (k * path_weight f xs)%N.
Proof.
  induction xs as [|x xs IH]; cbn [path_weight fold_right] in *; nia.
Qed.

Local Lemma path_weight_const {A} k (xs : list A) :
  path_weight (fun _ => k) xs = (k * N.of_nat (length xs))%N.
Proof.
  induction xs as [|x xs IH]; cbn [path_weight fold_right length].
  - nia.
  - rewrite Nat2N.inj_succ; nia.
Qed.

Local Lemma path_weight_map {A B} (f : A -> B) (charge : B -> N) xs :
  path_weight charge (map f xs) = path_weight (fun x => charge (f x)) xs.
Proof.
  induction xs as [|x xs IH]; cbn [path_weight fold_right map]; congruence.
Qed.



Local Lemma path_flat_length {A B} (f : A -> list B) xs :
  N.of_nat (length (flat_map f xs)) =
    path_weight (fun x => N.of_nat (length (f x))) xs.
Proof.
  induction xs as [|x xs IH]; cbn [flat_map].
  - reflexivity.
  - rewrite length_app, Nat2N.inj_add, IH; reflexivity.
Qed.

(** Mapping pays each callback once and one list step per occurrence. *)
Local Lemma path_map_time {A B} (f : A -> B) (clock : A -> N) xs :
  ListDef.T_map f clock xs = (path_weight clock xs + N.of_nat (length xs) + 1)%N.
Proof.
  induction xs as [|x xs IH]; time_unfold @ListDef.T_map;
    cbn [path_weight fold_right length] in *; rewrite ?Nat2N.inj_succ; nia.
Qed.

(** Flattening also pays for copying every callback output into the result. *)
Local Lemma path_flat_time {A B} (f : A -> list B) (clock : A -> N) xs :
  (Code.List.T_flat_map f clock xs <= path_weight clock xs +
    N.of_nat (length (flat_map f xs)) + 2 * N.of_nat (length xs) + 1)%N.
Proof.
  induction xs as [|x xs IH].
  - time_step.
  - pose proof (Datatypes.T_app_le (f x) (flat_map f xs)) as Happ.
    time_unfold @Code.List.T_flat_map.
    cbn [path_weight fold_right flat_map length] in *.
    rewrite length_app, Nat2N.inj_add, Nat2N.inj_succ; nia.
Qed.

(** A right fold pays a state-independent charge for each visited element. *)
Local Lemma path_fold_time {A B} (f : B -> A -> A) (clock : B -> A -> N)
    (charge : B -> N) xs a :
  (forall x acc, In x xs -> (clock x acc <= charge x)%N) ->
  (List.T_fold_right f clock a xs <=
    path_weight charge xs + N.of_nat (length xs) + 1)%N.
Proof.
  induction xs as [|x xs IH]; intro Hclock.
  - time_step.
  - pose proof (Hclock x (fold_right f a xs) (or_introl eq_refl)) as Hhead.
    specialize (IH (fun y acc Hy => Hclock y acc (or_intror Hy))).
    time_unfold @List.T_fold_right.
    cbn [path_weight fold_right length] in *; rewrite Nat2N.inj_succ; nia.
Qed.

(** A flat map combines callback budgets with the lengths of its actual outputs. *)
Local Lemma path_flat_comp {A B} (f : A -> list B) (clock reader : A -> N) xs k b :
  (forall x, In x xs ->
    (clock x <= reader x + k * N.of_nat (length (f x)) + b)%N) ->
  (Code.List.T_flat_map f clock xs <= path_weight reader xs +
    (k + 1) * N.of_nat (length (flat_map f xs)) +
    (b + 2) * N.of_nat (length xs) + 1)%N.
Proof.
  intro Hclock.
  pose proof (path_flat_time f clock xs) as Hflat.
  pose proof (path_weight_le clock
    (fun x => reader x + k * N.of_nat (length (f x)) + b)%N xs Hclock) as Hsum.
  rewrite !path_weight_add, path_weight_scale, path_weight_const,
    <- path_flat_length in Hsum; nia.
Qed.

(** A zero reader leaves only output and input traversal charges. *)
Local Lemma path_flat_linear {A B} (f : A -> list B) (clock : A -> N) xs k b :
  (forall x, In x xs -> (clock x <= k * N.of_nat (length (f x)) + b)%N) ->
  (Code.List.T_flat_map f clock xs <=
    (k + 1) * N.of_nat (length (flat_map f xs)) +
    (b + 2) * N.of_nat (length xs) + 1)%N.
Proof.
  intro Hclock.
  pose proof (path_flat_comp f clock (fun _ => 0%N) xs k b Hclock) as Hflat.
  rewrite path_weight_const in Hflat; nia.
Qed.

(** Pair preparation pays each flow callback once and copies every returned fact. *)
Lemma edge_pairs_time {E F} (flow : E -> F -> list F) T_flow facts e :
  (T_edge_pairs flow T_flow facts e <= path_weight (T_flow e) facts +
    3 * N.of_nat (length (edge_pairs flow facts e)) +
    4 * N.of_nat (length facts) + 2)%N.
Proof.
  time_unfold @T_edge_pairs.
  match goal with
  | |- context [Code.List.T_flat_map ?f ?clock facts] =>
    pose proof (path_flat_comp f clock (T_flow e) facts 2%N 2%N) as Hflat
  end.
  specialize (Hflat ltac:(intros x _; cbn beta;
    rewrite path_map_time, path_weight_const, length_map; nia)).
  unfold edge_pairs; nia.
Qed.

(** A return-bucket read pays for the bits of its site code. *)
Lemma return_rows_time {E F Site} code (index : ptrie (list (path_edge_info E F Site))) :
  (T_return_rows code index <=
    PTrieT.c_trie * N.of_nat (Pos.size_nat code + 1) + 1)%N.
Proof.
  pose proof (PTrieT.T_get_le (list (path_edge_info E F Site)) code index) as Hget.
  unfold PTrieT.T_get in Hget; time_unfold @T_return_rows; nia.
Qed.

(** Index construction pays once for each returned site's code and trie traversal. *)
Lemma return_index_time {E F Site} site_code T_site_code
    (infos : list (path_edge_info E F Site)) :
  (T_return_index site_code T_site_code infos <=
    path_weight (fun i => match info_kind i with
      | Return s => T_site_code s + 2 * PTrieT.c_trie *
        N.of_nat (Pos.size_nat (site_code s) + 1)
      | _ => 0
      end)%N infos + 4 * N.of_nat (length infos) + 2)%N.
Proof.
  time_unfold @T_return_index.
  match goal with
  | |- context [List.T_fold_right ?f ?clock Empty infos] =>
    pose proof (path_fold_time f clock (fun i =>
      3 + match info_kind i with
      | Return s => T_site_code s + 2 * PTrieT.c_trie *
        N.of_nat (Pos.size_nat (site_code s) + 1)
      | _ => 0
      end)%N infos Empty) as Hfold
  end.
  specialize (Hfold ltac:(intros [e k pairs] acc _;
    cbn beta iota zeta; unfold T_info_kind; cbn [info_kind];
    destruct k as [|site|site|site];
    try nia;
    pose proof (return_rows_time (site_code site) acc) as Hget;
    pose proof (PTrieT.T_set_le _ (site_code site)
      (PathEdgeInfo e (Return site) pairs :: return_rows (site_code site) acc) acc) as Hset;
    nia)).
  rewrite path_weight_add, path_weight_const in Hfold; nia.
Qed.

(** Preparing calls retains at most one occurrence per input edge. *)
Lemma path_calls_length_le {E F Site} site_code returns
    (infos : list (path_edge_info E F Site)) :
  length (path_calls site_code returns infos) <= length infos.
Proof.
  unfold path_calls; induction infos as [|i infos IH]; cbn [flat_map length].
  - reflexivity.
  - destruct (info_kind i); cbn [app length]; lia.
Qed.

(** Call preparation performs one site encoding and bucket read per call occurrence. *)
Lemma path_calls_time {E F Site} site_code T_site_code returns
    (infos : list (path_edge_info E F Site)) :
  (T_path_calls site_code T_site_code returns infos <=
    path_weight (fun i => match info_kind i with
      | Call s => T_site_code s + PTrieT.c_trie *
        N.of_nat (Pos.size_nat (site_code s) + 1)
      | _ => 0
      end)%N infos + 6 * N.of_nat (length infos) + 2)%N.
Proof.
  time_unfold @T_path_calls.
  match goal with
  | |- context [Code.List.T_flat_map ?f ?clock infos] =>
    pose proof (path_flat_comp f clock (fun i => match info_kind i with
      | Call s => T_site_code s + PTrieT.c_trie *
        N.of_nat (Pos.size_nat (site_code s) + 1)
      | _ => 0
      end)%N infos 0%N 3%N) as Hflat
  end.
  specialize (Hflat ltac:(intros [e k pairs] _;
    cbn beta iota zeta; unfold T_info_kind; cbn [info_kind];
    destruct k as [|site|site|site]; try nia;
    pose proof (return_rows_time (site_code site) returns) as Hget; nia)).
  pose proof (path_calls_length_le site_code returns infos) as Hlength.
  unfold path_calls in Hlength; nia.
Qed.

(** All cached fact-pair occurrences count, including pairs of unused returns. *)
Definition path_pair_mass {E F Site} (infos : list (path_edge_info E F Site)) : N :=
  path_weight (fun i => N.of_nat (length (info_pairs i))) infos.

(** Every matched return is visited even when either pair list is empty. *)
Definition path_match_mass {E F Site}
    (calls : list (path_edge_info E F Site * list (path_edge_info E F Site))) : N :=
  path_weight (fun call => N.of_nat (length (snd call)) *
    (1 + N.of_nat (length (info_pairs (fst call)))))%N calls.

(** Each call and return occurrence contributes one site charge. *)
Definition path_site_mass {E F Site} (charge : Site -> N)
    (infos : list (path_edge_info E F Site)) : N :=
  path_weight (fun i => match info_kind i with
    | Call site | Return site => charge site
    | _ => 0%N
    end) infos.

(** The separate phase budgets fit one structural envelope. *)
Local Lemma path_builder_arithmetic e d c p q s i j r : (c <= e)%N ->
  (3 * p + 4 * d * e + 18 * e + (4 * e + 4) * d +
    (4 * q + 4 * c + 4) * d + 3 * s + 4 * i + 5 * j + 6 * r + 13 <=
    64 * (1 + e * (d + 1) + d + p + d * q + (s + (i + (j + r)))))%N.
Proof.
  intro Hcalls.
  assert (Hscans : (d * c <= d * e)%N) by (apply N.mul_le_mono_l; exact Hcalls).
  nia.
Qed.

(** The builder pays callback sums, site widths, cached pairs, matched scans and output. *)
Theorem path_rules_fast_time {N E F Site} site_code T_site_code
    (kind : E -> edge_kind Site) T_kind (dst : E -> N) T_dst
    (facts : list F) flow T_flow (seeds : list (N * F)) edges :
  let infos := map (fun e => PathEdgeInfo e (kind e) (edge_pairs flow facts e)) edges in
  let index := return_index site_code infos in
  let calls := path_calls site_code index infos in
  (T_path_rules_fast site_code T_site_code kind T_kind dst T_dst
    facts flow T_flow seeds edges <=
    path_weight T_kind edges + path_weight (fun e => path_weight (T_flow e) facts) edges +
    path_site_mass T_site_code infos + 2 * PTrieT.c_trie *
      path_site_mass (fun s => N.of_nat (Pos.size_nat (site_code s) + 1)) infos +
    path_weight (fun i => match info_kind i with
      | Call _ => T_dst (info_edge i)
      | _ => 0%N
      end) infos +
    64 * (1 + N.of_nat (length edges) * (N.of_nat (length facts) + 1) +
      N.of_nat (length facts) + path_pair_mass infos +
      N.of_nat (length facts) * path_match_mass calls +
      N.of_nat (length (path_rules_fast site_code kind dst facts flow seeds edges))))%N.
Proof.
  intros infos index calls.
  assert (Hinfos : length infos = length edges) by (unfold infos; apply length_map).
  pose proof (path_calls_length_le site_code index infos) as Hcalls_length.
  fold calls in Hcalls_length.
  pose proof (return_index_time site_code T_site_code infos) as Hindex.
  pose proof (path_calls_time site_code T_site_code index infos) as Hcalls.
  assert (Hsites :
    (T_return_index site_code T_site_code infos +
     T_path_calls site_code T_site_code index infos <=
     path_site_mass T_site_code infos + 2 * PTrieT.c_trie *
       path_site_mass (fun s => N.of_nat (Pos.size_nat (site_code s) + 1)) infos +
     10 * N.of_nat (length infos) + 4)%N).
  {
    assert (Hcharges :
      (path_weight (fun i => match info_kind i with
        | Return s => T_site_code s + 2 * PTrieT.c_trie *
          N.of_nat (Pos.size_nat (site_code s) + 1)
        | _ => 0 end)%N infos +
       path_weight (fun i => match info_kind i with
        | Call s => T_site_code s + PTrieT.c_trie *
          N.of_nat (Pos.size_nat (site_code s) + 1)
        | _ => 0 end)%N infos <=
       path_site_mass T_site_code infos + 2 * PTrieT.c_trie *
         path_site_mass (fun s => N.of_nat (Pos.size_nat (site_code s) + 1)) infos)%N).
    {
      unfold path_site_mass.
      rewrite <- path_weight_scale, <- !path_weight_add.
      apply path_weight_le. intros [e k pairs] _; destruct k;
        cbn [info_kind]; nia.
    }
    nia.
  }
  clear Hindex Hcalls.
  unfold path_rules_fast, T_path_rules_fast.
  fold infos index calls.
  match goal with
  | |- context [ListDef.T_map ?f ?clock edges] =>
    assert (Hprepare : (ListDef.T_map f clock edges <=
      path_weight T_kind edges + path_weight (fun e => path_weight (T_flow e) facts) edges +
      3 * path_pair_mass infos + 4 * N.of_nat (length facts) * N.of_nat (length edges) +
      4 * N.of_nat (length edges) + 1)%N)
  end.
  {
    rewrite path_map_time.
    match goal with
    | |- (path_weight ?clock edges + _ + _ <= _)%N =>
      pose proof (path_weight_le clock (fun e => T_kind e + path_weight (T_flow e) facts +
        3 * N.of_nat (length (edge_pairs flow facts e)) +
        (4 * N.of_nat (length facts) + 3))%N edges) as Hsum
    end.
    specialize (Hsum ltac:(intros e _; cbn beta;
      pose proof (edge_pairs_time flow T_flow facts e) as Hpairs; nia)).
    unfold path_pair_mass, infos; rewrite path_weight_map; cbn [info_pairs].
    rewrite !path_weight_add, !path_weight_scale, !path_weight_const in Hsum.
    rewrite !path_weight_add, !path_weight_const.
    nia.
  }
  match type of Hprepare with
  | (?t <= _)%N => set (prepare_time := t) in *
  end.
  match goal with
  | |- context [Code.List.T_flat_map ?f ?clock infos] =>
    assert (Hidentities : (Code.List.T_flat_map f clock infos <=
      path_weight (fun i => match info_kind i with
        | Call _ => T_dst (info_edge i) | _ => 0%N end) infos +
      3 * N.of_nat (length (flat_map f infos)) + 4 * N.of_nat (length infos) + 1)%N)
  end.
  {
    eapply path_flat_comp with (k := 2%N) (b := 2%N).
    intros [e k pairs] _; destruct k; cbn beta iota zeta;
      cbn [info_kind info_edge];
      rewrite ?path_map_time, ?path_weight_const, ?length_map; nia.
  }
  match type of Hidentities with
  | (Code.List.T_flat_map ?f ?clock infos <= _)%N =>
    set (identity_rules := flat_map f infos) in *;
    set (identity_time := Code.List.T_flat_map f clock infos) in *
  end.
  match goal with
  | |- context [Code.List.T_flat_map ?f ?clock facts] =>
    assert (Hsteps : (Code.List.T_flat_map f clock facts <=
      4 * N.of_nat (length (flat_map f facts)) +
      (4 * N.of_nat (length infos) + 4) * N.of_nat (length facts) + 1)%N)
  end.
  {
    eapply N.le_trans.
    - eapply path_flat_linear with (k := 3%N)
        (b := (4 * N.of_nat (length infos) + 2)%N).
      intros d0 _; cbn beta.
      match goal with
      | |- context [Code.List.T_flat_map ?f ?clock infos] =>
        pose proof (path_flat_linear f clock infos 2%N 2%N) as Hinner
      end.
      specialize (Hinner ltac:(intros [e k pairs] _; destruct k; cbn beta iota zeta;
        rewrite ?path_map_time, ?path_weight_const, ?length_map; nia)).
      nia.
    - nia.
  }
  match type of Hsteps with
  | (Code.List.T_flat_map ?f ?clock facts <= _)%N =>
    set (step_rules := flat_map f facts) in *;
    set (step_time := Code.List.T_flat_map f clock facts) in *
  end.
  match goal with
  | |- context [Code.List.T_flat_map ?f ?clock facts] =>
    assert (Hreturns : (Code.List.T_flat_map f clock facts <=
      6 * N.of_nat (length (flat_map f facts)) +
      (4 * path_match_mass calls + 4 * N.of_nat (length calls) + 4) *
        N.of_nat (length facts) + 1)%N)
  end.
  {
    eapply N.le_trans.
    - eapply path_flat_linear with (k := 5%N)
        (b := (4 * path_match_mass calls + 4 * N.of_nat (length calls) + 2)%N).
      intros d0 _; cbn beta.
      match goal with
      | |- context [Code.List.T_flat_map ?f ?clock calls] =>
        pose proof (path_flat_comp f clock (fun call => 4 *
          (N.of_nat (length (snd call)) *
            (1 + N.of_nat (length (info_pairs (fst call))))))%N calls 4%N 2%N) as Hcall
      end.
      specialize (Hcall ltac:(intros [[ce ck cp] rets] _; cbn beta iota zeta;
        cbn [fst snd info_pairs];
        match goal with
        | |- context [Code.List.T_flat_map ?f ?clock rets] =>
          pose proof (path_flat_linear f clock rets 3%N
            (4 * N.of_nat (length cp) + 2)%N) as Hrets
        end;
        specialize (Hrets ltac:(intros [re rk rp] _; cbn beta iota zeta;
          match goal with
          | |- context [Code.List.T_flat_map ?f ?clock cp] =>
            pose proof (path_flat_linear f clock cp 2%N 2%N) as Hpairs
          end;
          specialize (Hpairs ltac:(intros [x a] _; cbn beta iota zeta;
            rewrite path_map_time, path_weight_const, length_map; nia)); nia)); nia)).
      rewrite path_weight_scale in Hcall; fold (path_match_mass calls) in Hcall; nia.
    - nia.
  }
  match type of Hreturns with
  | (Code.List.T_flat_map ?f ?clock facts <= _)%N =>
    set (return_rules := flat_map f facts) in *;
    set (return_time := Code.List.T_flat_map f clock facts) in *
  end.
  repeat match goal with
  | |- context [Datatypes.T_app ?xs ?ys] =>
    let Happend := fresh "Happend" in
    pose proof (Datatypes.T_app_le xs ys) as Happend;
    let append_time := fresh "append_time" in
    set (append_time := Datatypes.T_app xs ys) in *
  end.
  rewrite path_map_time, path_weight_const, !length_app, length_map, !Nat2N.inj_add.
  rewrite length_map in Happend1.
  rewrite Hinfos in *.
  assert (Hcalls_count : (N.of_nat (length calls) <= N.of_nat (length edges))%N) by lia.
  set (edge_count := N.of_nat (length edges)) in *.
  set (fact_count := N.of_nat (length facts)) in *.
  set (call_count := N.of_nat (length calls)) in *.
  set (seed_count := N.of_nat (length seeds)) in *.
  set (identity_count := N.of_nat (length identity_rules)) in *.
  set (step_count := N.of_nat (length step_rules)) in *.
  set (return_count := N.of_nat (length return_rules)) in *.
  set (pair_count := path_pair_mass infos) in *.
  set (match_count := path_match_mass calls) in *.
  set (kind_work := path_weight T_kind edges) in *.
  set (flow_work := path_weight (fun e => path_weight (T_flow e) facts) edges) in *.
  set (site_work := path_site_mass T_site_code infos) in *.
  set (width_work := (2 * PTrieT.c_trie *
    path_site_mass (fun s => N.of_nat (Pos.size_nat (site_code s) + 1)) infos)%N) in *.
  set (destination_work := path_weight (fun i => match info_kind i with
    | Call _ => T_dst (info_edge i) | _ => 0%N end) infos) in *.
  set (index_time := T_return_index site_code T_site_code infos) in *.
  set (calls_time := T_path_calls site_code T_site_code index infos) in *.
  clear Hinfos Hcalls_length.
  clearbody infos index calls prepare_time identity_rules identity_time step_rules step_time
    return_rules return_time.
  repeat match goal with x := _ : BinNums.N |- _ => clearbody x end.
  pose proof (path_builder_arithmetic edge_count fact_count call_count pair_count match_count
    seed_count identity_count step_count return_count Hcalls_count) as Harithmetic.
  lia.
Qed.


(** Pending dependencies are read in order and passed to the rule evaluator. *)
Definition path_query {N E F A} (finish : path_rule N E F -> list A -> A)
    (rule : path_rule N E F) (pending : list (path_edge N F)) (received : list A)
    : query (path_edge N F) A (path_frame N E F A) :=
  match pending with
  | nil => Ret (finish rule (rev_append received nil))
  | x :: xs => Ask x (PathFrame N E F A rule xs received)
  end.
TimeFun path_query.

Definition bool_query {N F} (pending : list (path_edge N F)) (acc : bool)
    : query (path_edge N F) bool (bool_frame N F) :=
  match pending with
  | nil => Ret acc
  | x :: xs => Ask x (BoolFrame N F xs acc)
  end.
TimeFun bool_query.

Module IfdsCode (P : TYPE) (N : KEY_OPS) (E : TYPE) (C : CFG_OPS P N E)
    (Site : KEY_OPS) (I : ICFG_OPS P N E C Site) (F : KEY_OPS)
    (FL : FLOW_FUN_OPS P N E F) (R : IFDS_RULES_OPS P N E F) (L : IFDS_LATTICE_OPS) <: IFDS_OPS P N E F L.
  Definition prog := P.t.
  Definition key := path_edge N.t F.t.
  Definition row := path_row N.t E.t F.t.
  Definition frame := bool_frame N.t F.t.
  Definition key_code := path_edge_code N.encode F.encode.
  Definition key_eqb (x y : key) :=
    F.eqb (fst x) (fst y) && N.eqb (fst (snd x)) (fst (snd y)) &&
      F.eqb (snd (snd x)) (snd (snd y)).
  Definition rows p : list row := path_number 1%positive
    (R.rules p).
  Definition target p (r : row) : key := match path_row_rule r with
    | PathIdentity n d => (d, (n, d))
    | PathStep d0 e _ y => (d0, (C.dst p e, y))
    | PathReturn d0 _ ret _ _ _ y => (d0, (C.dst p ret, y))
    end.
  Definition deps p (r : row) : list key := match path_row_rule r with
    | PathIdentity _ _ => nil
    | PathStep d0 e x _ => (d0, (C.src p e, x)) :: nil
    | PathReturn d0 call ret x a b _ =>
        (d0, (C.src p call, x)) :: (a, (C.src p ret, b)) :: nil
    end.
  Definition sides (_ : prog) (_ : row) : list key := nil.
  Definition start p (r : row) : query key bool frame := bool_query (deps p r) true.
  Definition resume (_ : prog) (f : frame) (a : bool) : query key bool frame :=
    bool_query (bool_frame_pending _ _ f) (bool_frame_acc _ _ f && a).
End IfdsCode.

Module IfdsLatticeCode <: IFDS_LATTICE_OPS.
  Definition t := bool.
  Definition leb (a b : bool) := negb a || b.
  Definition bot := false.
  Definition is_bot := negb.
  Definition join := orb.
End IfdsLatticeCode.

Module IfdsLattice <: IFDS_LATTICE.
  Include IfdsLatticeCode.
  (** Every value is below itself. *)
  Lemma leb_refl  : forall a, leb a a = true.
  Proof.
    intros []; reflexivity.
  Qed.
  (** The order composes through an intermediate value. *)
  Lemma leb_trans : forall a b c, leb a b = true -> leb b c = true -> leb a c = true.
  Proof.
    intros [] [] []; cbn [leb negb orb]; congruence.
  Qed.
  (** Bottom is below every value. *)
  Lemma bot_least : forall a, leb bot a = true.
  Proof.
    intros []; reflexivity.
  Qed.
  (** The bottom test recognizes bottom. *)
  Lemma is_bot_bot : is_bot bot = true.
  Proof.
    reflexivity.
  Qed.
  (** Every recognized bottom is below every value. *)
  Lemma is_bot_least : forall a b, is_bot a = true -> leb a b = true.
  Proof.
    intros [] []; cbn [is_bot leb negb orb]; congruence.
  Qed.
  (** Join is above its left operand. *)
  Lemma join_ub_l : forall a b, leb a (join a b) = true.
  Proof.
    intros [] []; reflexivity.
  Qed.
  (** Join is above its right operand. *)
  Lemma join_ub_r : forall a b, leb b (join a b) = true.
  Proof.
    intros [] []; reflexivity.
  Qed.
End IfdsLattice.

Module IfdsLatticeT <: IFDS_LATTICE_T.
  Include IfdsLattice.
  TimeFun leb.
  TimeFun is_bot.
  TimeFun join.

  Definition size (_ : t) := 1%nat.
  Definition c_lat : N := 1%N.
  Lemma c_lat_pos : (1 <= c_lat)%N.
  Proof.
    reflexivity.
  Qed.
  Lemma T_leb_le : forall a b,
    (T_leb a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros [] []; unfold c_lat, size; time_step.
  Qed.
  Lemma T_join_le : forall a b,
    (T_join a b <= c_lat * N.of_nat (size a + size b + 1))%N.
  Proof.
    intros [] []; unfold c_lat, size; time_step.
  Qed.
  Lemma T_is_bot_le : forall a,
    (T_is_bot a <= c_lat * N.of_nat (size a + 1))%N.
  Proof.
    intros []; unfold c_lat, size; time_step.
  Qed.
End IfdsLatticeT.

Module Ifds (P : TYPE) (N : KEY) (E : TYPE) (C : CFG P N E)
    (Site : KEY) (I : ICFG P N E C Site) (F : KEY)
    (FL : FLOW_FUN P N E C F) (R : IFDS_RULES P N E C Site I F FL) (L : IFDS_LATTICE) <: IFDS P N E C Site I F FL L.
  Include IfdsCode P N E C Site I F FL R L.
  Include SYSTEM_SPEC L.
  Definition wf (p : prog) := R.wf p.
  (** Codes distinguish all system keys. *)
  Lemma key_code_inj : forall a b, key_code a = key_code b -> a = b.
  Proof.
    intros [d [n x]] [d' [n' x']] Hcode.
    unfold key_code, path_edge_code, pair_code in Hcode; cbn [fst snd] in Hcode.
    destruct (glue_inj _ _ _ _ Hcode) as [Hd Hrest].
    destruct (glue_inj _ _ _ _ Hrest) as [Hn Hx].
    apply F.encode_inj in Hd; apply N.encode_inj in Hn; apply F.encode_inj in Hx.
    now subst.
  Qed.
  (** Key equality decides equality of system keys. *)
  Lemma key_eqb_spec : forall a b, reflect (a = b) (key_eqb a b).
  Proof.
    intros [d [n x]] [d' [n' x']].
    unfold key_eqb; cbn [fst snd].
    destruct (F.eqb_spec d d'), (N.eqb_spec n n'), (F.eqb_spec x x');
      cbn [andb]; constructor; congruence.
  Qed.
  (** Boolean rules combine the caller and callee at a matched return. *)
  Lemma eval_spec : forall p r look, eval p r look = Some
    (match path_row_rule r with
     | PathIdentity _ _ => true
     | PathStep d0 e x _ => look (d0, (C.src p e, x))
     | PathReturn d0 call ret x a b _ =>
         look (d0, (C.src p call, x)) && look (a, (C.src p ret, b))
     end, nil).
  Proof.
    intros p [code rule] look; destruct rule; reflexivity.
  Qed.
  (** Declared rows finish within their dependency-derived fuel. *)
  Lemma eval_total : forall p r look,
    wf p -> In r (rows p) -> eval p r look <> None.
  Proof.
    intros p r look _ _; rewrite eval_spec; discriminate.
  Qed.
  (** A row observes its declared dependencies. *)
  Lemma reads_within : forall p r s u, wf p -> In r (rows p) ->
    (forall x, In x (deps p r) -> s x = u x) -> eval p r s = eval p r u.
  Proof.
    intros p [code rule] s u _ _ Hagree.
    rewrite !eval_spec; destruct rule; cbn [path_row_rule] in *.
    - reflexivity.
    - rewrite (Hagree _ (or_introl eq_refl)); reflexivity.
    - rewrite (Hagree _ (or_introl eq_refl)),
        (Hagree _ (or_intror (or_introl eq_refl))); reflexivity.
  Qed.

  (** A continuing Boolean query only asks keys still present in its input list. *)
  Lemma bool_query_asks : forall p look n pending value q acc x f,
    loop_fuel (eval_step (resume p) look) n (bool_query pending value, nil) =
      inl (q, acc) ->
    fst (peel q acc) = inr (x, f) -> In x pending.
  Proof.
    intros p look n; induction n as [|n IH];
      intros pending value q acc x f Hloop Hask.
    - cbn [loop_fuel] in Hloop; injection Hloop as <- <-.
      destruct pending as [|y pending]; cbn [bool_query peel fst] in Hask.
      + discriminate.
      + injection Hask as <- <-; now left.
    - destruct pending as [|y pending];
        cbn [loop_fuel bool_query eval_step peel resume fst snd
          bool_frame_pending bool_frame_acc] in Hloop.
      + discriminate.
      + right; eapply IH; eassumption.
  Qed.
  (** A row asks only its declared dependencies. *)
  Lemma asks_within : forall p r look n q acc x f, wf p -> In r (rows p) ->
    loop_fuel (eval_step (resume p) look) n (start p r, nil) = inl (q, acc) ->
    fst (peel q acc) = inr (x, f) -> In x (deps p r).
  Proof.
    intros p r look n q acc x f _ _ Hloop Hask.
    eapply bool_query_asks; eassumption.
  Qed.
  (** Side contributions use declared side keys. *)
  Lemma sides_within : forall p r look a ss x b, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> In (x, b) ss -> In x (sides p r).
  Proof.
    intros p r look a ss x b _ _ Heval Hin.
    rewrite eval_spec in Heval; injection Heval as <- <-; contradiction.
  Qed.
  (** Side contributions fit the declared occurrence budget. *)
  Lemma sides_count : forall p r look a ss, wf p -> In r (rows p) ->
    eval p r look = Some (a, ss) -> length ss <= length (sides p r).
  Proof.
    intros p r look a ss _ _ Heval.
    rewrite eval_spec in Heval; injection Heval as <- <-; reflexivity.
  Qed.
  Include IFDS_SPEC P N E C Site I F FL L.
  (** The system encodes all three path-edge components. *)
  Lemma key_code_spec : key_code = path_edge_code N.encode F.encode.
  Proof.
    reflexivity.
  Qed.
  (** The row inventory contains exactly the enabled finite rules. *)
  Lemma rows_spec : forall p rule, wf p ->
    (exists r, In r (rows p) /\ path_row_rule r = rule) <-> enabled p rule.
  Proof.
    intros p rule Hwf; unfold rows, enabled.
    rewrite <- (R.rules_enabled p rule Hwf).
    split.
    - intros [r [Hin Hrule]]; rewrite <- Hrule.
      rewrite <- (path_number_rules 1%positive (R.rules p)).
      apply in_map; exact Hin.
    - intro Hin.
      assert (Hmap : In rule (map path_row_rule (path_number 1%positive (R.rules p)))).
      { now rewrite path_number_rules. }
      apply in_map_iff in Hmap; destruct Hmap as [r [Hrule Hr]].
      exists r; now split.
  Qed.
  (** Rule targets follow their destination edge or identity point. *)
  Lemma target_spec : forall p r, target p r =
    match path_row_rule r with
    | PathIdentity n d => (d, (n, d))
    | PathStep d0 e _ y => (d0, (C.dst p e, y))
    | PathReturn d0 _ ret _ _ _ y => (d0, (C.dst p ret, y))
    end.
  Proof.
    reflexivity.
  Qed.
End Ifds.

Module IfdsT (P : TYPE) (N : KEY_T) (E : KEY_T) (C : CFG_T P N E)
    (Site : KEY_T) (I : ICFG_T P N E C Site) (F : KEY_T)
    (FL : FLOW_FUN_T P N E C F) (R : IFDS_RULES_T P N E C Site I F FL)
    (L : IFDS_LATTICE_T) <: IFDS_T P N E C Site I F FL L.
  Include Ifds P N E C Site I F FL R L.

  TimeFun key_code.
  TimeFun key_eqb.
  TimeFun rows.
  TimeFun target.
  TimeFun deps.
  TimeFun sides.
  TimeFun start.
  TimeFun resume.
  Definition row_work p s := N.of_nat (length (rows p) + s + L.size true + 1).
  Definition path_kw (p : prog) : nat := fold_right Nat.max 0
    (flat_map (fun r => map key_bits (writes p r ++ deps p r)) (rows p)).
  Definition kw := path_kw.
  Definition c_sys : N := (64 * (N.c_key + F.c_key + C.c_cfg + R.c_rules + 1))%N.
  Lemma row_work_mono : forall p s t, s <= t ->
    (row_work p s <= row_work p t)%N.
  Proof.
    intros p s t Hst; unfold row_work; lia.
  Qed.

  (** A maximum bounds every width that occurs in its inventory. *)
  Lemma path_width_member : forall widths width, In width widths ->
    width <= fold_right Nat.max 0 widths.
  Proof.
    induction widths as [|head widths IH]; intros width Hin.
    - contradiction.
    - destruct Hin as [<-|Hin]; cbn [fold_right].
      + apply Nat.le_max_l.
      + eapply Nat.le_trans; [exact (IH width Hin)|apply Nat.le_max_r].
  Qed.
  Lemma key_bits_le : forall p r x, wf p -> In r (rows p) ->
    In x (writes p r ++ deps p r) -> key_bits x <= kw p.
  Proof.
    intros p r x _ Hr Hx; unfold kw, path_kw.
    apply path_width_member, in_flat_map.
    exists r; split; [exact Hr|now apply in_map].
  Qed.

  (** A path-edge code contains the widths of all three key components. *)
  Lemma path_key_bits : forall d n x,
    key_bits (d, (n, x)) + 2 = 2 * F.bits d + 2 * N.bits n + F.bits x.
  Proof.
    intros d n x; unfold key_bits, key_code, path_edge_code, pair_code.
    cbn [fst snd]; rewrite !glue_bits.
    unfold F.bits, N.bits.
    pose proof (Pos.size_nat_pos (F.encode d)).
    pose proof (Pos.size_nat_pos (N.encode n)).
    pose proof (Pos.size_nat_pos (F.encode x)); lia.
  Qed.

  (** Each component fits the code's common bit budget. *)
  Lemma path_key_widths : forall d n x,
    F.bits d <= key_bits (d, (n, x)) /\ N.bits n <= key_bits (d, (n, x)) /\
      F.bits x <= key_bits (d, (n, x)).
  Proof.
    intros d n x; pose proof (path_key_bits d n x) as Hbits.
    unfold F.bits, N.bits in *.
    pose proof (Pos.size_nat_pos (F.encode d)).
    pose proof (Pos.size_nat_pos (N.encode n)).
    pose proof (Pos.size_nat_pos (F.encode x)); lia.
  Qed.
  Lemma T_key_code_le : forall x,
    (T_key_code x <= c_sys * N.of_nat (key_bits x + 1))%N.
  Proof.
    intros [d [n x]].
    pose proof (F.T_encode_le d) as Hd.
    pose proof (N.T_encode_le n) as Hn.
    pose proof (F.T_encode_le x) as Hx.
    pose proof (T_glue_le (N.encode n) (F.encode x)) as Hinner.
    pose proof (T_glue_le (F.encode d) (glue (N.encode n) (F.encode x))) as Houter.
    destruct (path_key_widths d n x) as [Hd_width [Hn_width Hx_width]].
    set (budget := N.of_nat (key_bits (d, (n, x)) + 1)).
    set (scale := (N.c_key + F.c_key + C.c_cfg + R.c_rules + 1)%N).
    assert (Hd_cost : (F.T_encode d <= scale * budget)%N).
    { eapply N.le_trans; [exact Hd|]. apply N.mul_le_mono; unfold scale, budget; lia. }
    assert (Hn_cost : (N.T_encode n <= scale * budget)%N).
    { eapply N.le_trans; [exact Hn|]. apply N.mul_le_mono; unfold scale, budget; lia. }
    assert (Hx_cost : (F.T_encode x <= scale * budget)%N).
    { eapply N.le_trans; [exact Hx|]. apply N.mul_le_mono; unfold scale, budget; lia. }
    assert (Hinner_cost : (T_glue (N.encode n) (F.encode x) <= budget)%N).
    { unfold c_glue in Hinner; unfold N.bits in Hn_width; unfold budget; lia. }
    assert (Houter_cost :
      (T_glue (F.encode d) (glue (N.encode n) (F.encode x)) <= budget)%N).
    { unfold c_glue in Houter; unfold F.bits in Hd_width; unfold budget; lia. }
    assert (Hscale : (1 <= scale)%N) by (unfold scale; lia).
    assert (Hbudget : (1 <= budget)%N) by (unfold budget; lia).
    clear Hd Hn Hx Hinner Houter Hd_width Hn_width Hx_width.
    unfold c_sys; fold scale; fold budget.
    time_unfold T_key_code; time_unfold @T_path_edge_code; time_unfold @T_pair_code.
    time_simpl; time_cbn; time_unfold @T_pair_code.
    time_simpl; time_cbn; unfold pair_code; cbn [fst snd].
    fold scale; fold budget; clearbody scale budget; nia.
  Qed.
  Lemma T_key_eqb_le : forall a b,
    (T_key_eqb a b <= c_sys * N.of_nat (key_bits a + 1))%N.
  Proof.
    intros [d [n x]] [d' [n' x']].
    pose proof (F.T_eqb_le d d') as Hd.
    pose proof (N.T_eqb_le n n') as Hn.
    pose proof (F.T_eqb_le x x') as Hx.
    destruct (path_key_widths d n x) as [Hd_width [Hn_width Hx_width]].
    set (budget := N.of_nat (key_bits (d, (n, x)) + 1)).
    set (scale := (N.c_key + F.c_key + C.c_cfg + R.c_rules + 1)%N).
    assert (Hd_cost : (F.T_eqb d d' <= scale * budget)%N).
    { eapply N.le_trans; [exact Hd|]. apply N.mul_le_mono; unfold scale, budget; lia. }
    assert (Hn_cost : (N.T_eqb n n' <= scale * budget)%N).
    { eapply N.le_trans; [exact Hn|]. apply N.mul_le_mono; unfold scale, budget; lia. }
    assert (Hx_cost : (F.T_eqb x x' <= scale * budget)%N).
    { eapply N.le_trans; [exact Hx|]. apply N.mul_le_mono; unfold scale, budget; lia. }
    assert (Hscale : (1 <= scale)%N) by (unfold scale; lia).
    assert (Hbudget : (1 <= budget)%N) by (unfold budget; lia).
    clear Hd Hn Hx Hd_width Hn_width Hx_width.
    unfold c_sys; fold scale; fold budget.
    time_unfold T_key_eqb; time_simpl; time_cbn.
    fold scale; fold budget; clearbody scale budget; nia.
  Qed.
  Lemma T_rows_le : forall p, wf p ->
    (T_rows p <= c_sys * N.of_nat (length (rows p) + 1))%N.
  Proof.
    intros p _.
    pose proof (R.T_rules_le p) as Hrules.
    pose proof (T_path_number_le 1%positive (R.rules p)) as Hnumber.
    change (T_rows p <= c_sys *
      N.of_nat (length (path_number 1%positive (R.rules p)) + 1))%N.
    rewrite path_number_length; unfold c_sys.
    time_unfold T_rows; time_cbn_all; nia.
  Qed.
  Lemma T_target_le : forall p r, wf p -> In r (rows p) ->
    (T_target p r <= c_sys * (row_work p 0 + 1))%N.
  Proof.
    intros p [code rule] _ _; destruct rule; unfold c_sys, row_work; time_step.
  Qed.
  Lemma T_start_le : forall p r, wf p -> In r (rows p) ->
    (T_start p r <= c_sys * (row_work p 0 + 1))%N.
  Proof.
    intros p [code rule] _ _; destruct rule; unfold c_sys, row_work.
    all: time_unfold T_start; time_unfold T_deps; time_simpl; time_cbn; time_pose; nia.
  Qed.
  Lemma T_resume_le : forall p r look s n q acc x f, wf p -> In r (rows p) ->
    (forall y, L.size (look y) <= s) ->
    loop_fuel (eval_step (resume p) look) n (start p r, nil) = inl (q, acc) ->
    fst (peel q acc) = inr (x, f) ->
    (T_resume p f (look x) <= c_sys * (row_work p s + 1))%N.
  Proof.
    intros p r look s n q acc x [pending value] _ _ _ _ _.
    unfold c_sys, row_work; time_step.
  Qed.
  Lemma T_deps_le : forall p r, wf p -> In r (rows p) ->
    (T_deps p r <= c_sys * N.of_nat (length (deps p r) + 1) *
      N.of_nat (kw p + 1))%N.
  Proof.
    intros p [code rule] _ _; destruct rule; unfold c_sys; time_step.
  Qed.
  Lemma T_sides_le : forall p r, wf p -> In r (rows p) ->
    (T_sides p r <= c_sys * N.of_nat (length (sides p r) + 1) *
      N.of_nat (kw p + 1))%N.
  Proof.
    intros p r _ _; unfold c_sys; time_step.
  Qed.
  Lemma eval_size_le : forall p r look s a ss, wf p -> In r (rows p) ->
    (forall x, L.size (look x) <= s) -> eval p r look = Some (a, ss) ->
    (N.of_nat (L.size a) <= row_work p s)%N /\
    Forall (fun xb => (N.of_nat (L.size (snd xb)) <= row_work p s)%N) ss.
  Proof.
    intros p [code rule] look s a ss _ _ Hlook Heval.
    rewrite eval_spec in Heval; destruct rule as [n d|d0 e x y|d0 call ret x b c y];
      cbn [path_row_rule] in Heval.
    - injection Heval as <- <-; split; [unfold row_work; lia|constructor].
    - injection Heval as <- <-; split; [|constructor].
      pose proof (Hlook (d0, (C.src p e, x))); unfold row_work; lia.
    - destruct (look (d0, (C.src p call, x))) eqn:Hcaller;
        cbn [andb] in Heval; injection Heval as <- <-; split; try constructor.
      + pose proof (Hlook (b, (C.src p ret, c))); unfold row_work; lia.
      + pose proof (Hlook (d0, (C.src p call, x))) as Hsize.
        rewrite Hcaller in Hsize; unfold row_work; lia.
  Qed.
  (** Row enumeration is linear in the number of rows. *)
  Lemma rows_bigO : bigO (X := prog) (fun p => wf p)
    (fun p => N.of_nat (length (rows p))) (fun p => T_rows p).
  Proof.
    apply bigO_intro with (c := c_sys).
    intros p Hwf; pose proof (T_rows_le p Hwf) as Hrows.
    change (T_rows p <= c_sys * N.of_nat (length (rows p)) + c_sys)%N.
    rewrite Nat2N.inj_add in Hrows; nia.
  Qed.

  (** Starting a listed row fits its budget at the empty value. *)
  Lemma start_bigO : bigO (X := prog * row) (fun '(p, r) => wf p /\ In r (rows p))
    (fun '(p, _) => row_work p 0) (fun '(p, r) => T_start p r).
  Proof.
    apply bigO_intro with (c := c_sys).
    intros [p r] [Hwf Hrow].
    change (T_start p r <= c_sys * row_work p 0 + c_sys)%N.
    pose proof (T_start_le p r Hwf Hrow) as Htime; nia.
  Qed.

  (** Listing dependencies is linear in their number times the key width. *)
  Lemma deps_bigO : bigO (X := prog * row) (fun '(p, r) => wf p /\ In r (rows p))
    (fun '(p, r) => N.of_nat ((length (deps p r) + 1) * (kw p + 1)))
    (fun '(p, r) => T_deps p r).
  Proof.
    apply bigO_intro with (c := c_sys).
    intros [p r] [Hwf Hrow].
    change (T_deps p r <=
      c_sys * N.of_nat ((length (deps p r) + 1) * (kw p + 1)) + c_sys)%N.
    pose proof (T_deps_le p r Hwf Hrow) as Htime.
    rewrite Nat2N.inj_mul; nia.
  Qed.

  (** Finding a listed row's target fits its budget at the empty value. *)
  Lemma target_bigO : bigO (X := prog * row) (fun '(p, r) => wf p /\ In r (rows p))
    (fun '(p, _) => row_work p 0) (fun '(p, r) => T_target p r).
  Proof.
    apply bigO_intro with (c := c_sys).
    intros [p r] [Hwf Hrow].
    change (T_target p r <= c_sys * row_work p 0 + c_sys)%N.
    pose proof (T_target_le p r Hwf Hrow) as Htime; nia.
  Qed.

  (** Listing side writes is linear in their number times the key width. *)
  Lemma sides_bigO : bigO (X := prog * row) (fun '(p, r) => wf p /\ In r (rows p))
    (fun '(p, r) => N.of_nat ((length (sides p r) + 1) * (kw p + 1)))
    (fun '(p, r) => T_sides p r).
  Proof.
    apply bigO_intro with (c := c_sys).
    intros [p r] [Hwf Hrow].
    change (T_sides p r <=
      c_sys * N.of_nat ((length (sides p r) + 1) * (kw p + 1)) + c_sys)%N.
    pose proof (T_sides_le p r Hwf Hrow) as Htime.
    rewrite Nat2N.inj_mul; nia.
  Qed.
End IfdsT.

Module IfdsSound (P : TYPE) (N : KEY) (E : TYPE) (C : CFG P N E)
    (Site : KEY) (I : ICFG P N E C Site) (F : KEY) (FL : FLOW_FUN P N E C F)
    (L : IFDS_LATTICE) (A : IFDS P N E C Site I F FL L)
    <: IFDS_SOUND P N E C Site I F FL L A.
  (** A post-solution satisfies the implication described by each enabled rule. *)
  Lemma enabled_holds : forall p look, A.wf p -> A.post_solution p look ->
    forall rule, A.enabled p rule ->
      match rule with
      | PathIdentity n d => look (d, (n, d)) = true
      | PathStep d0 e x y =>
          look (d0, (C.src p e, x)) = true -> look (d0, (C.dst p e, y)) = true
      | PathReturn d0 call ret x a b y =>
          look (d0, (C.src p call, x)) = true ->
          look (a, (C.src p ret, b)) = true -> look (d0, (C.dst p ret, y)) = true
      end.
  Proof.
    intros p look Hwf Hpost rule Henabled.
    destruct (proj2 (A.rows_spec p rule Hwf) Henabled) as [r [Hin Hrule]].
    pose proof (Hpost r Hin) as Hrow.
    rewrite A.eval_spec, A.target_spec, Hrule in Hrow.
    destruct rule as [n d|d0 e x y|d0 call ret x a b y]; cbn [row_ok] in Hrow.
    - change (look (d, (n, d)) && true = true) in Hrow.
      now apply andb_prop in Hrow as [Hout _].
    - intro Hinput; rewrite Hinput in Hrow.
      change (look (d0, (C.dst p e, y)) && true = true) in Hrow.
      now apply andb_prop in Hrow as [Hout _].
    - intros Hcaller Hcallee; rewrite Hcaller, Hcallee in Hrow.
      change (look (d0, (C.dst p ret, y)) && true = true) in Hrow.
      now apply andb_prop in Hrow as [Hout _].
  Qed.

  (** Entering a listed call supplies an identity edge for each supported callee input. *)
  Lemma call_identity : forall p look, A.wf p -> A.post_solution p look ->
    forall call site x a, In call (C.edges p) -> I.kind p call = Call site ->
      In x (FL.facts p) -> In a (FL.flow p call x) ->
      look (a, (C.dst p call, a)) = true.
  Proof.
    intros p look Hwf Hpost call site x a Hcall Hkind Hx Ha.
    apply (enabled_holds p look Hwf Hpost (PathIdentity (C.dst p call) a)).
    right; exists call, site, x; repeat split; assumption || reflexivity.
  Qed.

  (** A matched return combines the suspended caller edge with the callee result. *)
  Lemma return_holds : forall p look, A.wf p -> A.post_solution p look ->
    forall d0 call ret site x a b y,
      In d0 (FL.facts p) -> In call (C.edges p) -> In ret (C.edges p) ->
      I.kind p call = Call site -> I.kind p ret = Return site ->
      In x (FL.facts p) -> In a (FL.flow p call x) -> In b (FL.facts p) ->
      In y (FL.flow p ret b) -> look (d0, (C.src p call, x)) = true ->
      look (a, (C.src p ret, b)) = true -> look (d0, (C.dst p ret, y)) = true.
  Proof.
    intros p look Hwf Hpost d0 call ret site x a b y Hd0 Hcall Hret
      Hcall_kind Hret_kind Hx Ha Hb Hy Hcaller Hcallee.
    apply (enabled_holds p look Hwf Hpost (PathReturn d0 call ret x a b y)).
    - split; [exact Hd0|]. split; [exact Hcall|]. split; [exact Hret|].
      split; [exists site; now split|].
      split; [exact Hx|]. split; [exact Ha|]. now split.
    - exact Hcaller.
    - exact Hcallee.
  Qed.

  (** Balanced paths preserve both finite fact support and their origin's path edge. *)
  Lemma path_propagates : forall p look, A.wf p -> A.post_solution p look ->
    forall n path m,
      valid_path (C.edges p) (C.src p) (C.dst p) (I.kind p) n path m ->
      forall d0 x y, In d0 (FL.facts p) -> In x (FL.facts p) ->
        look (d0, (n, x)) = true -> In y (path_facts (FL.flow p) x path) ->
        In y (FL.facts p) /\ look (d0, (m, y)) = true.
  Proof.
    intros p look Hwf Hpost n path m Hpath.
    induction Hpath as [n|e He Hkind|n m t left right Hleft IHleft Hright IHright|
      call ret site inside Hcall Hret Hcall_kind Hret_kind Hinside IHinside];
      intros d0 x y Hd0 Hx Hlook Hy.
    - cbn [path_facts fold_left] in Hy; destruct Hy as [<-|[]]; now split.
    - rewrite path_facts_single in Hy; split.
      + eapply FL.flow_closed; eassumption.
      + apply (enabled_holds p look Hwf Hpost (PathStep d0 e x y)).
        * split; [exact Hd0|]. split; [exact He|].
          split; [exact Hkind|]. now split.
        * exact Hlook.
    - rewrite path_facts_app in Hy; apply in_flat_map in Hy.
      destruct Hy as [z [Hz Hy]].
      destruct (IHleft d0 x z Hd0 Hx Hlook Hz) as [Hz_supported Hz_look].
      exact (IHright d0 z y Hd0 Hz_supported Hz_look Hy).
    - rewrite path_facts_cons in Hy; apply in_flat_map in Hy.
      destruct Hy as [a [Ha Hy]].
      rewrite path_facts_app in Hy; apply in_flat_map in Hy.
      destruct Hy as [b [Hb Hy]]; rewrite path_facts_single in Hy.
      pose proof (FL.flow_closed p call x a Hcall Hx Ha) as Ha_supported.
      pose proof (call_identity p look Hwf Hpost call site x a Hcall
        Hcall_kind Hx Ha) as Ha_look.
      destruct (IHinside a a b Ha_supported Ha_supported Ha_look Hb)
        as [Hb_supported Hb_look].
      split.
      + eapply FL.flow_closed; eassumption.
      + exact (return_holds p look Hwf Hpost d0 call ret site x a b y Hd0 Hcall Hret
          Hcall_kind Hret_kind Hx Ha Hb_supported Hy Hlook Hb_look).
  Qed.

  (** Every seeded balanced path is included in every Boolean post-solution. *)
  Lemma covers : forall p look, A.wf p -> A.post_solution p look ->
    forall entry d0 n path d, In (entry, d0) (FL.seeds p) ->
      valid_path (C.edges p) (C.src p) (C.dst p) (I.kind p) entry path n ->
      In d (path_facts (FL.flow p) d0 path) -> look (d0, (n, d)) = true.
  Proof.
    intros p look Hwf Hpost entry d0 n path d Hseed Hpath Hd.
    pose proof (FL.seeds_facts p entry d0 Hseed) as Hd0.
    assert (Hidentity : look (d0, (entry, d0)) = true).
    { apply (enabled_holds p look Hwf Hpost (PathIdentity entry d0)).
      now left. }
    exact (proj2 (path_propagates p look Hwf Hpost entry path n Hpath
      d0 d0 d Hd0 Hd0 Hidentity Hd)).
  Qed.
End IfdsSound.
