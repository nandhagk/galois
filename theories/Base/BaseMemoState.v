(** * Memo tables over growing registries

    Dense-ID caches retain the registry and cache produced by recursive misses.
    For example, a parent miss can allocate a child ID and retain its cached result.
    Builds on: BaseMemo, BaseIntern and the public BaseMap contracts. *)

From Stdlib Require Import NArith Lia.
From Galois.Cost Require Import CostMonad.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseMemo BaseIntern.
Import Cost.Notations.

Module MemoState.

(** A miss returns its result, its updated cache and its updated registry state. *)
Definition result R S := ((R * Memo.t positive R) * S)%type.

(** Defined meanings are stable when a registry grows. *)
Definition extends {R S} (meaning : S -> positive -> option R) (s s' : S) : Prop :=
  forall i value, meaning s i = Some value -> meaning s' i = Some value.

(** Cache entries have defined meanings in the same registry that accompanies the cache. *)
Definition valid {R S} (meaning : S -> positive -> option R) s
    (table : Memo.t positive R) : Prop :=
  Map.wf positive_encoding table /\
  forall i value, Map.get positive_encoding i table = Some value ->
    meaning s i = Some value.

(** Hits retain the current registry and misses insert into the child-produced cache. *)
Definition run_c {R S} i
    (miss_c : Memo.t positive R -> S -> Cost.t (result R S))
    (table : Memo.t positive R) (state : S) : Cost.t (result R S * bool) :=
  let* old := Map.get_c positive_encoding i table in
  match old with
  | Some value => Cost.ret (((value, table), state), true)
  | None =>
    Cost.step ;;
    let* fresh := miss_c table state in
    let '((value, updated), state') := fresh in
    let* stored := Map.set_c positive_encoding i value updated in
    Cost.ret (((value, stored), state'), false)
  end.

(** The plain operation projects the same costed callback execution. *)
Definition run {R S} i miss_c (table : Memo.t positive R) (state : S) :=
  Cost.value (run_c i miss_c table state).

(** A miss retains both components returned by its callback before storing the parent. *)
Theorem run_equation {R S} i miss_c (table : Memo.t positive R) (state : S) :
  run i miss_c table state =
    match Map.get positive_encoding i table with
    | Some value => (((value, table), state), true)
    | None =>
      let '((value, updated), state') := Cost.value (miss_c table state) in
      (((value, Map.set positive_encoding i value updated), state'), false)
    end.
Proof.
  unfold run, run_c. autorewrite with galois_cost.
  fold (Map.get positive_encoding i table).
  destruct (Map.get positive_encoding i table); [reflexivity|].
  destruct (Cost.value (miss_c table state)) as [[value updated] state'] eqn:Hmiss.
  autorewrite with galois_cost. rewrite Hmiss. autorewrite with galois_cost.
  reflexivity.
Qed.

(** Every registry extends itself. *)
Theorem extends_refl {R S} (meaning : S -> positive -> option R) state :
  extends meaning state state.
Proof.
  intros i value Hmeaning. exact Hmeaning.
Qed.

(** Consecutive registry extensions preserve all earlier defined meanings. *)
Theorem extends_trans {R S} (meaning : S -> positive -> option R) a b c :
  extends meaning a b -> extends meaning b c -> extends meaning a c.
Proof.
  intros Hab Hbc i value Hmeaning. apply Hbc, Hab, Hmeaning.
Qed.

(** Empty caches are valid even when no ID has a meaning yet. *)
Theorem valid_empty {R S} (meaning : S -> positive -> option R) state :
  valid meaning state Memo.empty.
Proof.
  split; [apply Map.wf_empty|].
  intros i value Hget. rewrite Map.get_empty in Hget. discriminate.
Qed.

(** Registry extension transports the same cache without recomputation or a default meaning. *)
Theorem valid_transport {R S} (meaning : S -> positive -> option R) state state' table :
  extends meaning state state' -> valid meaning state table -> valid meaning state' table.
Proof.
  intros Hextends [Hwf Hvalid]. split; [exact Hwf|].
  intros i value Hget. apply Hextends, Hvalid, Hget.
Qed.

(** Storing a defined result maintains the cache's reference relation. *)
Theorem valid_set {R S} (meaning : S -> positive -> option R) state table i value :
  valid meaning state table -> meaning state i = Some value ->
  valid meaning state (Map.set positive_encoding i value table).
Proof.
  intros [Hwf Hvalid] Hmeaning. split; [now apply Map.wf_set|].
  intros j found Hget. rewrite Map.get_set in Hget by exact Hwf.
  destruct (eqb_spec positive_encoding positive_encoding_laws j i) as [Heq|Hne].
  - subst j. injection Hget as <-. exact Hmeaning.
  - exact (Hvalid j found Hget).
Qed.

(** Agreement couples the returned cache to the returned registry and preserves its local laws. *)
Definition result_valid {R S} (meaning : S -> positive -> option R) (P : S -> Prop)
    (initial : S) (expected : R) (answer : result R S) : Prop :=
  let '((value, table), state) := answer in
  value = expected /\ valid meaning state table /\ P state /\ extends meaning initial state.

(** One local miss obligation suffices for recursive clients whose registry meanings grow. *)
Theorem run_agrees {R S} (meaning : S -> positive -> option R) (P : S -> Prop)
    i expected miss_c (table : Memo.t positive R) state :
  valid meaning state table -> P state -> meaning state i = Some expected ->
  result_valid meaning P state expected (Cost.value (miss_c table state)) ->
  result_valid meaning P state expected (fst (run i miss_c table state)).
Proof.
  intros Hvalid Hstate Hmeaning Hmiss. rewrite run_equation.
  destruct (Map.get positive_encoding i table) as [found|] eqn:Hget.
  - pose proof (proj2 Hvalid i found Hget) as Hfound.
    assert (Heq : found = expected) by congruence.
    cbn [fst result_valid]. split; [exact Heq|].
    split; [exact Hvalid|]. split; [exact Hstate|apply extends_refl].
  - destruct (Cost.value (miss_c table state)) as [[value updated] state'].
    destruct Hmiss as [Hvalue [Hupdated [Hstate' Hextends]]].
    cbn [fst result_valid]. split; [exact Hvalue|].
    split; [|now split].
    apply valid_set; [exact Hupdated|].
    rewrite Hvalue. apply Hextends, Hmeaning.
Qed.

(** Lookup, the selected miss and insertion into its returned cache give the exact charge. *)
Theorem run_cost_equation {R S} i miss_c (table : Memo.t positive R) (state : S) :
  Cost.ticks (run_c i miss_c table state) =
    (Cost.ticks (Map.get_c positive_encoding i table) +
      match Map.get positive_encoding i table with
      | Some _ => 0
      | None =>
        let '((value, updated), _) := Cost.value (miss_c table state) in
        1 + Cost.ticks (miss_c table state) +
          Cost.ticks (Map.set_c positive_encoding i value updated)
      end)%N.
Proof.
  unfold run_c. autorewrite with galois_cost.
  fold (Map.get positive_encoding i table).
  destruct (Map.get positive_encoding i table); autorewrite with galois_cost; [lia|].
  destruct (Cost.value (miss_c table state)) as [[value updated] state'].
  autorewrite with galois_cost. lia.
Qed.

(** Every attempt pays lookup and a miss retains its complete callback and insertion charges. *)
Theorem run_numeric_cost {R S} i miss_c (table : Memo.t positive R) (state : S) :
  (Cost.ticks (run_c i miss_c table state) <=
    3 + 4 * key_bits positive_encoding i + Cost.ticks (miss_c table state))%N.
Proof.
  rewrite run_cost_equation, Map.get_cost.
  pose proof (encode_cost_bound positive_encoding_cost_laws i) as Hencode.
  destruct (Map.get positive_encoding i table); [unfold key_bits in *; lia|].
  destruct (Cost.value (miss_c table state)) as [[value updated] state'].
  rewrite Map.set_cost. unfold key_bits in *. lia.
Qed.

(** An interner's inverse observation supplies defined meanings solely at allocated IDs. *)
Definition intern_meaning {K R} (f : K -> R) (state : Intern.t K) i :=
  option_map f (Intern.key_of i state).

(** Actual interning preserves every old inverse meaning through the public Intern contracts. *)
Theorem intern_extends {K R} (E : encoding K) (HE : encoding_laws E)
    (f : K -> R) key state :
  Intern.wf E state ->
  extends (intern_meaning f) state (snd (Intern.intern E key state)).
Proof.
  intros Hwf i value Hmeaning. unfold intern_meaning in *.
  destruct (Intern.key_of i state) as [old|] eqn:Hkey; [|discriminate].
  pose proof (Intern.find_key_of E old i state Hwf Hkey) as Hfind.
  pose proof (Intern.find_intern_old E HE old key i state Hwf Hfind) as Hretained.
  rewrite (Intern.key_of_find E old i _ (Intern.intern_wf E HE key state Hwf) Hretained).
  exact Hmeaning.
Qed.

Arguments run_c {R S} i miss_c table state : simpl never.
Arguments run {R S} i miss_c table state : simpl never.

End MemoState.
