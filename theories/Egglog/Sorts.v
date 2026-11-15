(** * Sorts of engine rules

    Rules are typed against the argument sorts and output kinds of their declarations, and a
    checker decides the typing in one pass over the rule text.
    For example, [mul(x, y) = z => Union z x] is well sorted when [mul] takes two classes,
    and [R(x, y) => Union x y] is rejected when [R] takes two values.
    Builds on: Syntax, Model, binary tries and Argent. *)

From Stdlib Require Import List PArith NArith Bool.
From Argent Require Import Time Std.
From Galois.Base Require Import Trie.
From Galois.Egglog Require Import Syntax Model.

Import List.ListNotations.

(** * Contexts and the judgment *)

(** A context gives some variables a sort. *)
Definition ctx := positive -> option sort.

Definition ctx_empty : ctx := fun _ => None.

Definition ctx_set (g : ctx) (x : positive) (s : sort) : ctx :=
  fun y => if Pos.eqb x y then Some s else g y.

(** A term has a sort when it is a variable of that sort or a literal at the value sort. *)
Definition has {V} (g : ctx) (t : term V) (s : sort) : Prop :=
  match t with
  | Var x => g x = Some s
  | Lit _ => s = SVal
  end.

(** A result term agrees with the output sort, and a relation has no result. *)
Definition has_result {V} (g : ctx) (out : output) (res : option (term V)) : Prop :=
  match out_sort out, res with
  | None, None => True
  | Some s, Some t => has g t s
  | _, _ => False
  end.

(** Binding a term at a position checks a bound variable and adds an unbound one. *)
Inductive binds {V : Type} (g : ctx) : term V -> sort -> ctx -> Prop :=
  | binds_old x s : g x = Some s -> binds g (Var x) s g
  | binds_new x s : g x = None -> binds g (Var x) s (ctx_set g x s)
  | binds_lit v : binds g (Lit v) SVal g.

Inductive binds_list {V : Type} : ctx -> list (term V) -> list sort -> ctx -> Prop :=
  | binds_nil g : binds_list g [] [] g
  | binds_cons g g1 g2 t ts s ss :
      binds g t s g1 -> binds_list g1 ts ss g2 -> binds_list g (t :: ts) (s :: ss) g2.

Definition binds_result {V} (g : ctx) (out : output) (res : option (term V))
    (g' : ctx) : Prop :=
  match out_sort out, res with
  | None, None => g' = g
  | Some s, Some t => binds g t s g'
  | _, _ => False
  end.

(** A query is well sorted when each function atom names a declared function with matching
    argument and result sorts and reads an argument or an output, and each primitive atom reads
    values bound before it. The engine joins function atoms on their columns, so a query cannot
    read a nullary relation. Actions can still write one. *)
Inductive query_ok {V : Type} (sorts : positive -> option (list sort))
    (kinds : positive -> option output) : ctx -> list (atom V) -> ctx -> Prop :=
  | query_nil g : query_ok sorts kinds g [] g
  | query_fun g g1 g2 g3 f args res ss out rest :
      sorts f = Some ss -> kinds f = Some out -> (ss <> [] \/ out <> ORel) ->
      binds_list g args ss g1 ->
      binds_result g1 out res g2 -> query_ok sorts kinds g2 rest g3 ->
      query_ok sorts kinds g (Fun V f args res :: rest) g3
  | query_prim g g1 p args res rest :
      Forall (fun t => has g t SVal) args -> has g res SVal ->
      query_ok sorts kinds g rest g1 ->
      query_ok sorts kinds g (Prim V p args res :: rest) g1.

(** Actions are well sorted when every argument has its declared sort, [Make] targets a
    constructor and binds a class, [Let] binds a value and [Union] joins two classes. *)
Fixpoint actions_ok {V} (sorts : positive -> option (list sort))
    (kinds : positive -> option output) (g : ctx) (acts : list (action V)) : Prop :=
  match acts with
  | [] => True
  | a :: rest =>
      match a with
      | Make x f args =>
          exists ss, sorts f = Some ss /\ kinds f = Some OId /\ Forall2 (has g) args ss /\
            actions_ok sorts kinds (ctx_set g x SId) rest
      | Put f args res =>
          exists ss out, sorts f = Some ss /\ kinds f = Some out /\
            Forall2 (has g) args ss /\ has_result g out res /\ actions_ok sorts kinds g rest
      | Union t u => has g t SId /\ has g u SId /\ actions_ok sorts kinds g rest
      | Let x _ args =>
          Forall (fun t => has g t SVal) args /\
            actions_ok sorts kinds (ctx_set g x SVal) rest
      end
  end.

(** A rule is well sorted when its query types its variables and its actions use them. *)
Definition rule_ok {V} (sorts : positive -> option (list sort))
    (kinds : positive -> option output) (r : rule V) : Prop :=
  exists g, query_ok sorts kinds ctx_empty (query V r) g /\
    actions_ok sorts kinds g (actions V r).

(** A program is well sorted when every rule is well sorted against its declarations. *)
Definition program_ok {V} (p : program V) : Prop :=
  Forall (rule_ok (program_sorts p) (program_kind p)) (rules V p).

(** * Sorted rows, environments and models *)

(** A row has the argument sorts of its function and the output sort of its kind. *)
Definition row_sorted {V} (sorts : positive -> option (list sort))
    (kinds : positive -> option output) (f : positive) (k : list (cell V))
    (o : option (cell V)) : Prop :=
  exists out, sorts f = Some (map cell_sort k) /\ kinds f = Some out /\
    option_map cell_sort o = out_sort out.

(** Every row of a view is well sorted. *)
Definition view_sorted {V} (sorts : positive -> option (list sort))
    (w : view (V := V)) : Prop :=
  forall f k o, row w f k o -> row_sorted sorts (kind w) f k o.

(** An environment binds every variable of a context to a cell of its sort. *)
Definition env_sorted {V} (g : ctx) (s : env (V := V)) : Prop :=
  forall x t, g x = Some t -> exists c, s x = Some c /\ cell_sort c = t.

(** An environment is well sorted for the variables that the query of a rule binds. *)
Definition rule_env {V} (sorts : positive -> option (list sort))
    (kinds : positive -> option output) (r : rule V) (s : env (V := V)) : Prop :=
  exists g, query_ok sorts kinds ctx_empty (query V r) g /\ env_sorted g s.

(** A model value is a class or a value. *)
Definition value_sort {C V : Type} (c : C + V) : sort :=
  match c with
  | inl _ => SId
  | inr _ => SVal
  end.

(** A model environment binds every variable of a context to a value of its sort. *)
Definition model_env_sorted {V} (M : model (V := V)) (g : ctx) (s : model_env M) : Prop :=
  forall x t, g x = Some t -> exists c, s x = Some c /\ value_sort c = t.

(** A rule is valid in a model when its actions hold in every well-sorted environment that
    satisfies its query. *)
Definition rule_valid_sorted {V} (prim : positive -> list V -> option V)
    (M : model (V := V)) (sorts : positive -> option (list sort))
    (kinds : positive -> option output) (r : rule V) : Prop :=
  forall g s, query_ok sorts kinds ctx_empty (query V r) g -> model_env_sorted M g s ->
    Forall (model_atom prim M kinds s) (query V r) ->
    model_actions prim M kinds s (actions V r).

(** A program is valid in a model on well-sorted environments, and its lattice functions are
    closed under their merges. *)
Definition valid_sorted {V} (prim : positive -> list V -> option V)
    (merge : positive -> V -> V -> V) (M : model (V := V)) (p : program V) : Prop :=
  Forall (rule_valid_sorted prim M (program_sorts p) (program_kind p)) (rules V p) /\
  (forall f m k a b, program_kind p f = Some (OLat m) ->
    lat M f k a -> lat M f k b -> lat M f k (merge m a b)).

(** * The checker *)

Definition sort_eqb (a b : sort) : bool :=
  match a, b with
  | SId, SId => true
  | SVal, SVal => true
  | _, _ => false
  end.
TimeFun sort_eqb.

Definition has_b {V} (g : ptrie sort) (t : term V) (s : sort) : bool :=
  match t with
  | Var x =>
      match trie_get x g with
      | Some s' => sort_eqb s' s
      | None => false
      end
  | Lit _ => sort_eqb s SVal
  end.
TimeFun has_b.

Fixpoint has_list_b {V} (g : ptrie sort) (ts : list (term V)) (ss : list sort) : bool :=
  match ts, ss with
  | [], [] => true
  | t :: ts', s :: ss' => has_b g t s && has_list_b g ts' ss'
  | _, _ => false
  end.
TimeFun has_list_b.

Fixpoint has_vals_b {V} (g : ptrie sort) (ts : list (term V)) : bool :=
  match ts with
  | [] => true
  | t :: rest => has_b g t SVal && has_vals_b g rest
  end.
TimeFun has_vals_b.

Definition has_result_b {V} (g : ptrie sort) (out : output) (res : option (term V)) : bool :=
  match out_sort out, res with
  | None, None => true
  | Some s, Some t => has_b g t s
  | _, _ => false
  end.
TimeFun has_result_b.

Definition bind_b {V} (g : ptrie sort) (t : term V) (s : sort) : option (ptrie sort) :=
  match t with
  | Var x =>
      match trie_get x g with
      | Some s' => if sort_eqb s' s then Some g else None
      | None => Some (PTrieCode.set x s g)
      end
  | Lit _ => if sort_eqb s SVal then Some g else None
  end.
TimeFun bind_b.

Fixpoint bind_list_b {V} (g : ptrie sort) (ts : list (term V)) (ss : list sort)
    : option (ptrie sort) :=
  match ts, ss with
  | [], [] => Some g
  | t :: ts', s :: ss' =>
      match bind_b g t s with
      | Some g1 => bind_list_b g1 ts' ss'
      | None => None
      end
  | _, _ => None
  end.
TimeFun bind_list_b.

Definition bind_result_b {V} (g : ptrie sort) (out : output) (res : option (term V))
    : option (ptrie sort) :=
  match out_sort out, res with
  | None, None => Some g
  | Some s, Some t => bind_b g t s
  | _, _ => None
  end.
TimeFun bind_result_b.

(** The first declaration of a name wins, as in [lookup_sorts] and [lookup_kind]. *)
Fixpoint decl_table (ds : list decl) : ptrie (list sort * output) :=
  match ds with
  | [] => Empty
  | d :: rest => PTrieCode.set (name d) (arg_sorts d, out d) (decl_table rest)
  end.
TimeFun decl_table.

(** A function atom reads a column when its function takes an argument or has an output. *)
Definition reads_b (ss : list sort) (out : output) : bool :=
  match ss, out with
  | [], ORel => false
  | _, _ => true
  end.
TimeFun reads_b.

Fixpoint bind_query_b {V} (tb : ptrie (list sort * output)) (g : ptrie sort)
    (q : list (atom V)) : option (ptrie sort) :=
  match q with
  | [] => Some g
  | a :: rest =>
      match a with
      | Fun _ f args res =>
          match trie_get f tb with
          | Some (ss, out) =>
              if reads_b ss out then
                match bind_list_b g args ss with
                | Some g1 =>
                    match bind_result_b g1 out res with
                    | Some g2 => bind_query_b tb g2 rest
                    | None => None
                    end
                | None => None
                end
              else None
          | None => None
          end
      | Prim _ _ args res =>
          if has_vals_b g args && has_b g res SVal then bind_query_b tb g rest else None
      end
  end.
TimeFun bind_query_b.

Fixpoint check_actions_b {V} (tb : ptrie (list sort * output)) (g : ptrie sort)
    (acts : list (action V)) : bool :=
  match acts with
  | [] => true
  | a :: rest =>
      match a with
      | Make x f args =>
          match trie_get f tb with
          | Some (ss, OId) =>
              has_list_b g args ss && check_actions_b tb (PTrieCode.set x SId g) rest
          | _ => false
          end
      | Put f args res =>
          match trie_get f tb with
          | Some (ss, out) =>
              has_list_b g args ss && has_result_b g out res && check_actions_b tb g rest
          | None => false
          end
      | Union t u => has_b g t SId && has_b g u SId && check_actions_b tb g rest
      | Let x _ args => has_vals_b g args && check_actions_b tb (PTrieCode.set x SVal g) rest
      end
  end.
TimeFun check_actions_b.

Definition check_rule {V} (tb : ptrie (list sort * output)) (r : rule V) : bool :=
  match r with
  | Rule _ q acts =>
      match bind_query_b tb Empty q with
      | Some g => check_actions_b tb g acts
      | None => false
      end
  end.
TimeFun check_rule.

Fixpoint check_rules {V} (tb : ptrie (list sort * output)) (rs : list (rule V)) : bool :=
  match rs with
  | [] => true
  | r :: rest => check_rule tb r && check_rules tb rest
  end.
TimeFun check_rules.

Definition check_program {V} (p : program V) : bool :=
  check_rules (decl_table (decls V p)) (rules V p).
TimeFun check_program.

(** * Sizes *)

Definition term_bits {V} (t : term V) : nat :=
  match t with
  | Var x => Pos.size_nat x + 1
  | Lit _ => 1
  end.

Definition terms_bits {V} (ts : list (term V)) : nat :=
  fold_right (fun t n => term_bits t + n) 0 ts.

Definition result_bits {V} (res : option (term V)) : nat :=
  match res with
  | Some t => term_bits t
  | None => 0
  end.

Definition atom_bits {V} (a : atom V) : nat :=
  match a with
  | Fun _ f args res => Pos.size_nat f + terms_bits args + result_bits res + 1
  | Prim _ _ args res => terms_bits args + term_bits res + 1
  end.

Definition action_bits {V} (a : action V) : nat :=
  match a with
  | Make x f args => Pos.size_nat x + Pos.size_nat f + terms_bits args + 1
  | Put f args res => Pos.size_nat f + terms_bits args + result_bits res + 1
  | Union t u => term_bits t + term_bits u + 1
  | Let x _ args => Pos.size_nat x + terms_bits args + 1
  end.

Definition rule_bits {V} (r : rule V) : nat :=
  fold_right (fun a n => atom_bits a + n) 0 (query V r) +
  fold_right (fun a n => action_bits a + n) 0 (actions V r) + 1.

Definition decl_bits (d : decl) : nat := Pos.size_nat (name d) + length (arg_sorts d) + 1.

(** The bits of every name, variable and list cell of a program. *)
Definition program_bits {V} (p : program V) : nat :=
  fold_right (fun d n => decl_bits d + n) 0 (decls V p) +
  fold_right (fun r n => rule_bits r + n) 0 (rules V p) + 1.

(** * Lemmas *)

(** The column test accepts exactly the functions that take an argument or have an output. *)
Lemma reads_b_spec : forall ss out, reads_b ss out = true <-> ss <> [] \/ out <> ORel.
Proof.
  intros [|s ss] out; [destruct out as [| |m]|]; cbn [reads_b].
  - split; [discriminate|]. intros [Hss|Hout]; exfalso; [apply Hss|apply Hout]; reflexivity.
  - split; [intros _; right; discriminate|intros _; reflexivity].
  - split; [intros _; right; discriminate|intros _; reflexivity].
  - split; [intros _; left; discriminate|intros _; reflexivity].
Qed.

(** The checker decides well-sortedness. *)
Lemma check_program_spec : forall V (p : program V),
  check_program p = true <-> program_ok p.
Proof.
  intros V p.
  pose (rep := fun (tr : ptrie sort) (g : ctx) => forall x, trie_get x tr = g x).
  assert (Hempty : rep Empty ctx_empty).
  { intro x. apply PTrie.get_empty. }
  assert (Hset : forall tr g x ty, rep tr g ->
    rep (PTrieCode.set x ty tr) (ctx_set g x ty)).
  {
    intros tr g x ty Hrep y. unfold ctx_set.
    destruct (Pos.eqb x y) eqn:Hxy.
    - apply Pos.eqb_eq in Hxy. subst y. apply PTrie.get_set_same.
    - rewrite PTrie.get_set_other; [apply Hrep|].
      apply Pos.eqb_neq in Hxy. congruence.
  }
  assert (Heqb : forall a b, sort_eqb a b = true <-> a = b).
  { intros [] []; cbn [sort_eqb]; split; congruence. }
  assert (Hhas : forall tr g (t : term V) ty, rep tr g ->
    has_b tr t ty = true <-> has g t ty).
  {
    intros tr g [x|v] ty Hrep; cbn [has_b has].
    - rewrite Hrep. destruct (g x) as [ty'|]; [rewrite Heqb|]; split; congruence.
    - apply Heqb.
  }
  assert (Hhas_list : forall tr g (ts : list (term V)) ss, rep tr g ->
    has_list_b tr ts ss = true <-> Forall2 (has g) ts ss).
  {
    intros tr g ts. induction ts as [|t ts IH]; intros [|ty ss] Hrep;
      cbn [has_list_b]; try (split; [discriminate|intro H; inversion H]).
    - split; [intro; constructor|intro; reflexivity].
    - rewrite andb_true_iff, (Hhas tr g t ty Hrep), (IH ss Hrep).
      split.
      + intros [Ht Hts]. constructor; assumption.
      + intro H. inversion H; subst. split; assumption.
  }
  assert (Hhas_vals : forall tr g (ts : list (term V)), rep tr g ->
    has_vals_b tr ts = true <-> Forall (fun t => has g t SVal) ts).
  {
    intros tr g ts. induction ts as [|t ts IH]; intro Hrep; cbn [has_vals_b].
    - split; [intro; constructor|intro; reflexivity].
    - rewrite andb_true_iff, (Hhas tr g t SVal Hrep), (IH Hrep).
      split.
      + intros [Ht Hts]. constructor; assumption.
      + intro H. inversion H; subst. split; assumption.
  }
  assert (Hhas_result : forall tr g out (res : option (term V)), rep tr g ->
    has_result_b tr out res = true <-> has_result g out res).
  {
    intros tr g out [t|] Hrep; destruct out;
      cbn [has_result_b has_result out_sort]; try (split; tauto || discriminate).
    all: apply Hhas; exact Hrep.
  }
  assert (Hbind_sound : forall tr g (t : term V) ty tr', rep tr g ->
    bind_b tr t ty = Some tr' -> exists g', binds g t ty g' /\ rep tr' g').
  {
    intros tr g [x|v] ty tr' Hrep Hcheck; cbn [bind_b] in Hcheck.
    - destruct (trie_get x tr) as [ty'|] eqn:Hlookup.
      + destruct (sort_eqb ty' ty) eqn:Hty; [|discriminate].
        apply Heqb in Hty. subst ty'. inversion Hcheck; subst tr'.
        exists g. split; [apply binds_old; rewrite <- Hrep; exact Hlookup|exact Hrep].
      + inversion Hcheck; subst tr'. exists (ctx_set g x ty). split.
        * apply binds_new. rewrite <- Hrep. exact Hlookup.
        * apply Hset. exact Hrep.
    - destruct (sort_eqb ty SVal) eqn:Hty; [|discriminate].
      apply Heqb in Hty. subst ty. inversion Hcheck; subst tr'.
      exists g. split; [constructor|exact Hrep].
  }
  assert (Hbind_complete : forall tr g (t : term V) ty g', rep tr g ->
    binds g t ty g' -> exists tr', bind_b tr t ty = Some tr' /\ rep tr' g').
  {
    intros tr g t ty g' Hrep Hb. destruct Hb as [x ty Hlookup | x ty Hlookup | v].
    - exists tr. split; [|exact Hrep]. cbn [bind_b]. rewrite Hrep, Hlookup.
      rewrite (proj2 (Heqb ty ty) eq_refl). reflexivity.
    - exists (PTrieCode.set x ty tr). split.
      + cbn [bind_b]. rewrite Hrep, Hlookup. reflexivity.
      + apply Hset. exact Hrep.
    - exists tr. split; [reflexivity|exact Hrep].
  }
  assert (Hbind_list_sound : forall ts ss tr g tr', rep tr g ->
    @bind_list_b V tr ts ss = Some tr' ->
    exists g', binds_list g ts ss g' /\ rep tr' g').
  {
    induction ts as [|t ts IH]; intros [|ty ss] tr g tr' Hrep Hcheck;
      cbn [bind_list_b] in Hcheck; try discriminate.
    - inversion Hcheck; subst tr'. exists g. split; [constructor|exact Hrep].
    - destruct (bind_b tr t ty) as [tr1|] eqn:Hhead; [|discriminate].
      destruct (Hbind_sound tr g t ty tr1 Hrep Hhead) as [g1 [Hb Hrep1]].
      destruct (IH ss tr1 g1 tr' Hrep1 Hcheck) as [g' [Hbs Hrep']].
      exists g'. split; [econstructor; eauto|exact Hrep'].
  }
  assert (Hbind_list_complete : forall tr g ts ss g', rep tr g ->
    @binds_list V g ts ss g' ->
    exists tr', bind_list_b tr ts ss = Some tr' /\ rep tr' g').
  {
    intros tr g ts ss g' Hrep Hb. revert tr Hrep.
    induction Hb as [g | g g1 g2 t ts ty ss Hhead Htail IH]; intros tr Hrep.
    - exists tr. split; [reflexivity|exact Hrep].
    - destruct (Hbind_complete tr g t ty g1 Hrep Hhead) as [tr1 [Hcheck1 Hrep1]].
      destruct (IH tr1 Hrep1) as [tr2 [Hcheck2 Hrep2]].
      exists tr2. split; [cbn [bind_list_b]; rewrite Hcheck1; exact Hcheck2|exact Hrep2].
  }
  assert (Hbind_result_sound : forall tr g out res tr', rep tr g ->
    @bind_result_b V tr out res = Some tr' ->
    exists g', binds_result g out res g' /\ rep tr' g').
  {
    intros tr g out [t|] tr' Hrep Hcheck; destruct out;
      cbn [bind_result_b binds_result out_sort] in *; try discriminate.
    - eapply Hbind_sound; eauto.
    - eapply Hbind_sound; eauto.
    - inversion Hcheck; subst tr'. exists g. split; [reflexivity|exact Hrep].
  }
  assert (Hbind_result_complete : forall tr g out res g', rep tr g ->
    @binds_result V g out res g' ->
    exists tr', bind_result_b tr out res = Some tr' /\ rep tr' g').
  {
    intros tr g out [t|] g' Hrep Hb; destruct out;
      cbn [bind_result_b binds_result out_sort] in *; try contradiction.
    - eapply Hbind_complete; eauto.
    - eapply Hbind_complete; eauto.
    - subst g'. exists tr. split; [reflexivity|exact Hrep].
  }
  assert (Htable : forall f ss out,
    trie_get f (decl_table (decls V p)) = Some (ss, out) <->
    program_sorts p f = Some ss /\ program_kind p f = Some out).
  {
    unfold program_sorts, program_kind. generalize (decls V p). intro ds.
    induction ds as [|d ds IH]; intros f ss out; cbn [decl_table lookup_sorts lookup_kind].
    - rewrite PTrie.get_empty. split; [discriminate|intros [H _]; discriminate].
    - destruct (Pos.eqb (name d) f) eqn:Hname.
      + apply Pos.eqb_eq in Hname. subst f. rewrite PTrie.get_set_same.
        split; [intro H; inversion H; subst; split; reflexivity|intros [Hss Hout]; congruence].
      + rewrite PTrie.get_set_other.
        * apply IH.
        * apply Pos.eqb_neq in Hname. congruence.
  }
  assert (Hactions : forall acts tr g, rep tr g ->
    @check_actions_b V (decl_table (decls V p)) tr acts = true <->
    actions_ok (program_sorts p) (program_kind p) g acts).
  {
    induction acts as [|a acts IH]; intros tr g Hrep; cbn [check_actions_b actions_ok].
    - split; [intro; exact I|intro; reflexivity].
    - destruct a as [x f args | f args res | t u | x op args].
      + destruct (trie_get f (decl_table (decls V p))) as [[ss out]|] eqn:Hlookup.
        * destruct (proj1 (Htable f ss out) Hlookup) as [Hss Hout].
          destruct out; try (split; [discriminate|intros [ss' [_ [Hbad _]]]; congruence]).
          rewrite andb_true_iff, (Hhas_list tr g args ss Hrep),
            (IH _ _ (Hset tr g x SId Hrep)).
          split.
          -- intros [Hargs Hrest]. exists ss. repeat split; assumption.
          -- intros [ss' [Hss' [_ [Hargs Hrest]]]]. assert (ss' = ss) by congruence.
             subst ss'. split; assumption.
        * split; [discriminate|]. intros [ss [Hss [Hout _]]].
          pose proof (proj2 (Htable f ss OId) (conj Hss Hout)). congruence.
      + destruct (trie_get f (decl_table (decls V p))) as [[ss out]|] eqn:Hlookup.
        * destruct (proj1 (Htable f ss out) Hlookup) as [Hss Hout].
          rewrite !andb_true_iff, (Hhas_list tr g args ss Hrep),
            (Hhas_result tr g out res Hrep), (IH tr g Hrep).
          split.
          -- intros [[Hargs Hres] Hrest]. exists ss, out. repeat split; assumption.
          -- intros [ss' [out' [Hss' [Hout' [Hargs [Hres Hrest]]]]]].
             assert (ss' = ss) by congruence. assert (out' = out) by congruence.
             subst ss' out'. repeat split; assumption.
        * split; [discriminate|]. intros [ss [out [Hss [Hout _]]]].
          pose proof (proj2 (Htable f ss out) (conj Hss Hout)). congruence.
      + rewrite !andb_true_iff, (Hhas tr g t SId Hrep), (Hhas tr g u SId Hrep),
          (IH tr g Hrep). tauto.
      + rewrite andb_true_iff, (Hhas_vals tr g args Hrep),
          (IH _ _ (Hset tr g x SVal Hrep)). tauto.
  }
  assert (Hquery_sound : forall q tr g tr', rep tr g ->
    @bind_query_b V (decl_table (decls V p)) tr q = Some tr' ->
    exists g', query_ok (program_sorts p) (program_kind p) g q g' /\ rep tr' g').
  {
    induction q as [|a q IH]; intros tr g tr' Hrep Hcheck; cbn [bind_query_b] in Hcheck.
    - inversion Hcheck; subst tr'. exists g. split; [constructor|exact Hrep].
    - destruct a as [f args res | op args res].
      + destruct (trie_get f (decl_table (decls V p))) as [[ss out]|] eqn:Hlookup;
          [|discriminate].
        destruct (reads_b ss out) eqn:Hreads; [|discriminate].
        apply reads_b_spec in Hreads.
        destruct (bind_list_b tr args ss) as [tr1|] eqn:Hargs; [|discriminate].
        destruct (bind_result_b tr1 out res) as [tr2|] eqn:Hres; [|discriminate].
        destruct (proj1 (Htable f ss out) Hlookup) as [Hss Hout].
        destruct (Hbind_list_sound args ss tr g tr1 Hrep Hargs) as [g1 [Hb Hrep1]].
        destruct (Hbind_result_sound tr1 g1 out res tr2 Hrep1 Hres) as [g2 [Hr Hrep2]].
        destruct (IH tr2 g2 tr' Hrep2 Hcheck) as [g' [Hq Hrep']].
        exists g'. split; [econstructor; eauto|exact Hrep'].
      + destruct (has_vals_b tr args && has_b tr res SVal) eqn:Hargs; [|discriminate].
        apply andb_true_iff in Hargs. destruct Hargs as [Hargs Hres].
        apply (Hhas_vals tr g args Hrep) in Hargs. apply (Hhas tr g res SVal Hrep) in Hres.
        destruct (IH tr g tr' Hrep Hcheck) as [g' [Hq Hrep']].
        exists g'. split; [econstructor; eauto|exact Hrep'].
  }
  assert (Hquery_complete : forall tr g q g', rep tr g ->
    @query_ok V (program_sorts p) (program_kind p) g q g' ->
    exists tr', bind_query_b (decl_table (decls V p)) tr q = Some tr' /\ rep tr' g').
  {
    intros tr g q g' Hrep Hq. revert tr Hrep.
    induction Hq as
      [g | g g1 g2 g3 f args res ss out rest Hss Hout Hreads Hargs Hres Hrest IH
         | g g1 op args res rest Hargs Hres Hrest IH]; intros tr Hrep.
    - exists tr. split; [reflexivity|exact Hrep].
    - destruct (Hbind_list_complete tr g args ss g1 Hrep Hargs) as [tr1 [Hb Hrep1]].
      destruct (Hbind_result_complete tr1 g1 out res g2 Hrep1 Hres) as [tr2 [Hr Hrep2]].
      destruct (IH tr2 Hrep2) as [tr3 [Hq Hrep3]]. exists tr3. split; [|exact Hrep3].
      cbn [bind_query_b]. rewrite (proj2 (Htable f ss out) (conj Hss Hout)),
        (proj2 (reads_b_spec ss out) Hreads), Hb, Hr.
      exact Hq.
    - destruct (IH tr Hrep) as [tr' [Hq Hrep']]. exists tr'. split; [|exact Hrep'].
      cbn [bind_query_b]. rewrite (proj2 (Hhas_vals tr g args Hrep) Hargs),
        (proj2 (Hhas tr g res SVal Hrep) Hres). exact Hq.
  }
  assert (Hrule : forall r : rule V, check_rule (decl_table (decls V p)) r = true <->
    rule_ok (program_sorts p) (program_kind p) r).
  {
    intros [q acts]. cbn [check_rule rule_ok query actions]. split.
    - destruct (bind_query_b (decl_table (decls V p)) Empty q) as [tr|] eqn:Hq;
        [|discriminate]. intro Hacts.
      destruct (Hquery_sound q Empty ctx_empty tr Hempty Hq) as [g [Htyped Hrep]].
      exists g. split; [exact Htyped|]. apply (Hactions acts tr g Hrep). exact Hacts.
    - intros [g [Htyped Hacts]].
      destruct (Hquery_complete Empty ctx_empty q g Hempty Htyped) as [tr [Hq Hrep]].
      rewrite Hq. apply (Hactions acts tr g Hrep). exact Hacts.
  }
  unfold check_program, program_ok. generalize (rules V p). intro rs.
  induction rs as [|r rs IH]; cbn [check_rules].
  - split; [intro; constructor|intro; reflexivity].
  - rewrite andb_true_iff, Hrule, IH. split.
    + intros [Hr Hrs]. constructor; assumption.
    + intro H. inversion H; subst. split; assumption.
Qed.

Definition c_sorts : N := 2048.

(** Checking pays for each bit of the program text once. *)
Lemma T_check_program_le : forall V (p : program V),
  (T_check_program p <= c_sorts * N.of_nat (program_bits p + 1))%N.
Proof.
  Import Lia Tactics.
  intros V p. unfold c_sorts.
  assert (Hset : forall A x (a : A) tr,
    (PTrieCode.T_set x a tr <= 9 * N.of_nat (Pos.size_nat x + 1))%N).
  {
    intros A x a tr. pose proof (PTrieT.replace_clock_bound A x (Some a) tr).
    time_step.
  }
  assert (Hterm : forall t : term V, 1 <= term_bits t).
  { intros [x|v]; cbn [term_bits]; lia. }
  assert (Hhas : forall g (t : term V) s,
    (T_has_b g t s <= 8 * N.of_nat (term_bits t))%N).
  {
    intros g [x|v] s; time_step;
      unfold T_sort_eqb; time_cbn; rewrite ?PTrieT.trie_get_clock; time_cases; nia.
  }
  assert (Hhas_list : forall (ts : list (term V)) ss g,
    (T_has_list_b g ts ss <= 16 * N.of_nat (terms_bits ts + 1))%N).
  {
    induction ts as [|t ts IH]; intros [|s ss] g; time_step.
    pose proof (Hhas g t s). pose proof (IH ss g). pose proof (Hterm t).
    unfold terms_bits in *. cbn [fold_right] in *. nia.
  }
  assert (Hhas_vals : forall (ts : list (term V)) g,
    (T_has_vals_b g ts <= 16 * N.of_nat (terms_bits ts + 1))%N).
  {
    induction ts as [|t ts IH]; intro g; time_step.
    pose proof (Hhas g t SVal). pose proof (IH g). pose proof (Hterm t).
    unfold terms_bits in *. cbn [fold_right] in *. nia.
  }
  assert (Hhas_result : forall g out (res : option (term V)),
    (T_has_result_b g out res <= 16 * N.of_nat (result_bits res + 1))%N).
  {
    intros g out [t|]; destruct out; time_step;
      pose proof (Hhas g t SId); pose proof (Hhas g t SVal); unfold result_bits; nia.
  }
  assert (Hbind : forall g (t : term V) s,
    (T_bind_b g t s <= 16 * N.of_nat (term_bits t))%N).
  {
    intros g [x|v] s; time_step;
      unfold T_sort_eqb; time_cbn; rewrite ?PTrieT.trie_get_clock;
      try pose proof (Hset sort x s g); time_cases; nia.
  }
  assert (Hbind_list : forall (ts : list (term V)) ss g,
    (T_bind_list_b g ts ss <= 32 * N.of_nat (terms_bits ts + 1))%N).
  {
    induction ts as [|t ts IH]; intros [|s ss] g; time_step.
    pose proof (Hbind g t s). pose proof (Hterm t).
    destruct (bind_b g t s) as [g'|]; time_cbn.
    - pose proof (IH ss g'). unfold terms_bits in *. cbn [fold_right] in *. nia.
    - unfold terms_bits in *. cbn [fold_right] in *. nia.
  }
  assert (Hbind_result : forall g out (res : option (term V)),
    (T_bind_result_b g out res <= 32 * N.of_nat (result_bits res + 1))%N).
  {
    intros g out [t|]; destruct out; time_step;
      pose proof (Hbind g t SId); pose proof (Hbind g t SVal); unfold result_bits; nia.
  }
  assert (Hdecls : forall ds,
    (T_decl_table ds <= 16 * N.of_nat
      (S (fold_right (fun d n => (decl_bits d + n)%nat) 0%nat ds)))%N).
  {
    induction ds as [|d ds IH]; time_step.
    pose proof (Hset (list sort * output)%type (name d) (arg_sorts d, out d)
      (decl_table ds)).
    unfold decl_bits in *. nia.
  }
  assert (Hquery : forall (q : list (atom V)) tb g,
    (T_bind_query_b tb g q <= 128 * N.of_nat
      (S (fold_right (fun a n => (atom_bits a + n)%nat) 0%nat q)))%N).
  {
    induction q as [|a q IH]; intros tb g.
    - time_step.
    - destruct a as [f args res | op args res].
      + time_step. rewrite PTrieT.trie_get_clock.
        destruct (trie_get f tb) as [[ss out]|]; time_cbn; [|nia].
        destruct (reads_b ss out); time_cbn; [|nia].
        pose proof (Hbind_list args ss g).
        destruct (bind_list_b g args ss) as [g1|]; time_cbn; [|nia].
        pose proof (Hbind_result g1 out res).
        destruct (bind_result_b g1 out res) as [g2|]; time_cbn; [|nia].
        pose proof (IH tb g2). nia.
      + time_step.
  }
  assert (Hactions : forall (acts : list (action V)) tb g,
    (T_check_actions_b tb g acts <= 128 * N.of_nat
      (S (fold_right (fun a n => (action_bits a + n)%nat) 0%nat acts)))%N).
  {
    induction acts as [|a acts IH]; intros tb g.
    - time_step.
    - destruct a as [x f args | f args res | t u | x op args].
      + time_step. rewrite PTrieT.trie_get_clock.
        destruct (trie_get f tb) as [[ss out]|]; time_cbn; [|nia].
        destruct out; time_cbn; try nia.
        pose proof (Hhas_list args ss g). pose proof (Hset sort x SId g).
        pose proof (IH tb (PTrieCode.set x SId g)). nia.
      + time_step. rewrite PTrieT.trie_get_clock.
        destruct (trie_get f tb) as [[ss out]|]; time_cbn; [|nia].
        pose proof (Hhas_list args ss g). pose proof (Hhas_result g out res).
        pose proof (IH tb g). nia.
      + time_step.
      + time_step.
  }
  assert (Hrule : forall (r : rule V) tb,
    (T_check_rule tb r <= 512 * N.of_nat (rule_bits r))%N).
  {
    intros [q acts] tb. pose proof (Hquery q tb Empty).
    time_step.
  }
  assert (Hrules : forall (rs : list (rule V)) tb,
    (T_check_rules tb rs <= 1024 * N.of_nat
      (S (fold_right (fun r n => (rule_bits r + n)%nat) 0%nat rs)))%N).
  {
    induction rs as [|r rs IH]; intro tb; time_step.
    pose proof (Hrule r tb). pose proof (IH tb).
    assert (1 <= rule_bits r) by (unfold rule_bits; lia). nia.
  }
  pose proof (Hdecls (decls V p)).
  pose proof (Hrules (rules V p) (decl_table (decls V p))).
  time_step. unfold program_bits. nia.
Qed.

(** A match of a well-sorted query binds every variable of its context to a cell of its sort. *)
Lemma matches_rule_env : forall V prim (w : view (V := V)) sorts kinds (r : rule V) g s,
  view_sorted sorts w -> (forall f, kind w f = kinds f) ->
  query_ok sorts kinds ctx_empty (query V r) g -> matches prim w (query V r) s ->
  env_sorted g s.
Proof.
  intros V prim w sorts kinds r g s Hrows Hkinds Hquery Hmatches.
  assert (Hbind : forall g t ty g' (s : env (V := V)) c,
    binds g t ty g' -> env_sorted g s -> term_value s t c -> cell_sort c = ty ->
    env_sorted g' s).
  {
    intros h t ty h' e c Hbind Henv Hvalue Hsort.
    destruct Hbind as [x ty Hlookup | x ty Hlookup | v].
    - exact Henv.
    - intros y u. unfold ctx_set. destruct (Pos.eqb x y) eqn:Hxy.
      + apply Pos.eqb_eq in Hxy. subst y. intros Hu. inversion Hu; subst u.
        exists c. split; assumption.
      + apply Henv.
    - exact Henv.
  }
  assert (Hlist : forall g ts ss g' (cs : list (cell V)) s,
    binds_list g ts ss g' -> terms_value s ts cs -> map cell_sort cs = ss ->
    env_sorted g s -> env_sorted g' s).
  {
    intros h ts ss h' cs e Hb. revert cs.
    induction Hb as [h | h h1 h2 t ts ty ss Hhead Htail IH];
      intros cs Hvalues Hsort Henv.
    - exact Henv.
    - inversion Hvalues as [|t' c ts' cs' Hvalue Hvalues']; subst.
      cbn in Hsort. injection Hsort as Hcell Hcells.
      apply (IH cs' Hvalues' Hcells).
      eapply Hbind; eauto.
  }
  assert (Hresult : forall g out res g' o (s : env (V := V)),
    binds_result g out res g' ->
    (match res, o with
     | None, None => True
     | Some t, Some c => term_value s t c
     | _, _ => False
     end) ->
    option_map cell_sort o = out_sort out -> env_sorted g s -> env_sorted g' s).
  {
    intros h out res h' o e Hb Hvalue Hsort Henv.
    destruct out, res as [t|], o as [c|];
      cbn [binds_result out_sort option_map] in *; try contradiction; try discriminate.
    - subst h'. exact Henv.
    - injection Hsort as Hsort. eapply Hbind; eauto.
    - injection Hsort as Hsort. eapply Hbind; eauto.
  }
  assert (Hquery_env : forall h q h' (e : env (V := V)),
    query_ok sorts kinds h q h' -> matches prim w q e ->
    env_sorted h e -> env_sorted h' e).
  {
    intros h q h' e Htyped.
    induction Htyped as
      [h | h h1 h2 h3 f args res ss out rest Hss Hout _ Hargs Hres Hrest IH
         | h h1 p args res rest Hargs Hres Hrest IH]; intros Hmatch Henv.
    - exact Henv.
    - inversion Hmatch as [|a q' Hatom Htail]; subst.
      destruct Hatom as [k [o [Hvalues [Hvalue Hrow]]]].
      destruct (Hrows f k o Hrow) as [out' [Hss' [Hout' Hsort]]].
      rewrite Hkinds, Hout in Hout'. inversion Hout'; subst out'.
      assert (Hcells : map cell_sort k = ss) by congruence.
      apply IH; [exact Htail|].
      eapply Hresult; [exact Hres|exact Hvalue|exact Hsort|].
      eapply Hlist; eauto.
    - inversion Hmatch as [|a q' Hatom Htail]; subst.
      apply IH; assumption.
  }
  eapply Hquery_env; [exact Hquery|exact Hmatches|].
  intros x ty Hempty. discriminate Hempty.
Qed.

(** Validity in every environment gives validity in well-sorted environments. *)
Lemma valid_sorted_of_valid : forall V prim merge (M : model (V := V)) (p : program V),
  valid prim merge M p -> valid_sorted prim merge M p.
Proof.
  intros V prim merge M p [Hrules Hmerge].
  split.
  - apply Forall_forall. intros r Hin g s Hquery Hsorted Hmatches.
    apply (Hrules r s Hin Hmatches).
  - exact Hmerge.
Qed.

(** * Pointwise checker reflection *)

(** The empty trie agrees pointwise with the empty context. *)
Lemma trie_ctx_empty : forall x, trie_get x (@Empty sort) = ctx_empty x.
Proof.
  intro x. apply PTrie.get_empty.
Qed.

(** Trie updates agree pointwise with context updates. *)
Lemma trie_ctx_set : forall tr g x ty, (forall x, trie_get x tr = g x) ->
  (forall y, trie_get y (PTrieCode.set x ty tr) = ctx_set g x ty y).
Proof.
  intros tr g x ty Hrep y. unfold ctx_set.
  destruct (Pos.eqb x y) eqn:Hxy.
  - apply Pos.eqb_eq in Hxy. subst y. apply PTrie.get_set_same.
  - rewrite PTrie.get_set_other; [apply Hrep|].
    apply Pos.eqb_neq in Hxy. congruence.
Qed.

(** The sort comparison decides equality. *)
Lemma sort_eqb_spec : forall a b, sort_eqb a b = true <-> a = b.
Proof.
  intros [] []; cbn [sort_eqb]; split; congruence.
Qed.

(** The term checker reflects its declarative sort judgment. *)
Lemma has_b_spec : forall V tr g (t : term V) ty, (forall x, trie_get x tr = g x) ->
  has_b tr t ty = true <-> has g t ty.
Proof.
  intros V.
  intros tr g [x|v] ty Hrep; cbn [has_b has].
  - rewrite Hrep. destruct (g x) as [ty'|]; [rewrite sort_eqb_spec|]; split; congruence.
  - apply sort_eqb_spec.
Qed.

(** The argument checker reflects the pairwise sort judgment. *)
Lemma has_list_b_spec : forall V tr g (ts : list (term V)) ss, (forall x, trie_get x tr = g x) ->
  has_list_b tr ts ss = true <-> Forall2 (has g) ts ss.
Proof.
  intros V.
  intros tr g ts. induction ts as [|t ts IH]; intros [|ty ss] Hrep;
    cbn [has_list_b]; try (split; [discriminate|intro H; inversion H]).
  - split; [intro; constructor|intro; reflexivity].
  - rewrite andb_true_iff, (has_b_spec V tr g t ty Hrep), (IH ss Hrep).
    split.
    + intros [Ht Hts]. constructor; assumption.
    + intro H. inversion H; subst. split; assumption.
Qed.

(** The primitive-argument checker reflects value sorts. *)
Lemma has_vals_b_spec : forall V tr g (ts : list (term V)), (forall x, trie_get x tr = g x) ->
  has_vals_b tr ts = true <-> Forall (fun t => has g t SVal) ts.
Proof.
  intros V.
  intros tr g ts. induction ts as [|t ts IH]; intro Hrep; cbn [has_vals_b].
  - split; [intro; constructor|intro; reflexivity].
  - rewrite andb_true_iff, (has_b_spec V tr g t SVal Hrep), (IH Hrep).
    split.
    + intros [Ht Hts]. constructor; assumption.
    + intro H. inversion H; subst. split; assumption.
Qed.

(** The result checker reflects the declared output sort. *)
Lemma has_result_b_spec : forall V tr g out (res : option (term V)),
  (forall x, trie_get x tr = g x) ->
  has_result_b tr out res = true <-> has_result g out res.
Proof.
  intros V.
  intros tr g out [t|] Hrep; destruct out;
    cbn [has_result_b has_result out_sort]; try (split; tauto || discriminate).
  all: apply (has_b_spec V); exact Hrep.
Qed.

(** A successful term binding constructs an agreeing context. *)
Lemma bind_b_sound : forall V tr g (t : term V) ty tr', (forall x, trie_get x tr = g x) ->
  bind_b tr t ty = Some tr' -> exists g', binds g t ty g' /\ (forall x, trie_get x tr' = g' x).
Proof.
  intros V.
  intros tr g [x|v] ty tr' Hrep Hcheck; cbn [bind_b] in Hcheck.
  - destruct (trie_get x tr) as [ty'|] eqn:Hlookup.
    + destruct (sort_eqb ty' ty) eqn:Hty; [|discriminate].
      apply sort_eqb_spec in Hty. subst ty'. inversion Hcheck; subst tr'.
      exists g. split; [apply binds_old; rewrite <- Hrep; exact Hlookup|exact Hrep].
    + inversion Hcheck; subst tr'. exists (ctx_set g x ty). split.
      * apply binds_new. rewrite <- Hrep. exact Hlookup.
      * apply trie_ctx_set. exact Hrep.
  - destruct (sort_eqb ty SVal) eqn:Hty; [|discriminate].
    apply sort_eqb_spec in Hty. subst ty. inversion Hcheck; subst tr'.
    exists g. split; [constructor|exact Hrep].
Qed.

(** A declarative term binding is accepted by its agreeing trie. *)
Lemma bind_b_complete : forall V tr g (t : term V) ty g', (forall x, trie_get x tr = g x) ->
  binds g t ty g' -> exists tr', bind_b tr t ty = Some tr' /\ (forall x, trie_get x tr' = g' x).
Proof.
  intros V.
  intros tr g t ty g' Hrep Hb. destruct Hb as [x ty Hlookup | x ty Hlookup | v].
  - exists tr. split; [|exact Hrep]. cbn [bind_b]. rewrite Hrep, Hlookup.
    rewrite (proj2 (sort_eqb_spec ty ty) eq_refl). reflexivity.
  - exists (PTrieCode.set x ty tr). split.
    + cbn [bind_b]. rewrite Hrep, Hlookup. reflexivity.
    + apply trie_ctx_set. exact Hrep.
  - exists tr. split; [reflexivity|exact Hrep].
Qed.

(** Successful argument binding constructs an agreeing context. *)
Lemma bind_list_b_sound : forall V ts ss tr g tr', (forall x, trie_get x tr = g x) ->
  @bind_list_b V tr ts ss = Some tr' ->
  exists g', binds_list g ts ss g' /\ (forall x, trie_get x tr' = g' x).
Proof.
  intros V.
  induction ts as [|t ts IH]; intros [|ty ss] tr g tr' Hrep Hcheck;
    cbn [bind_list_b] in Hcheck; try discriminate.
  - inversion Hcheck; subst tr'. exists g. split; [constructor|exact Hrep].
  - destruct (bind_b tr t ty) as [tr1|] eqn:Hhead; [|discriminate].
    destruct (bind_b_sound V tr g t ty tr1 Hrep Hhead) as [g1 [Hb Hrep1]].
    destruct (IH ss tr1 g1 tr' Hrep1 Hcheck) as [g' [Hbs Hrep']].
    exists g'. split; [econstructor; eauto|exact Hrep'].
Qed.

(** Declarative argument binding is accepted by an agreeing trie. *)
Lemma bind_list_b_complete : forall V tr g ts ss g', (forall x, trie_get x tr = g x) ->
  @binds_list V g ts ss g' ->
  exists tr', bind_list_b tr ts ss = Some tr' /\ (forall x, trie_get x tr' = g' x).
Proof.
  intros V.
  intros tr g ts ss g' Hrep Hb. revert tr Hrep.
  induction Hb as [g | g g1 g2 t ts ty ss Hhead Htail IH]; intros tr Hrep.
  - exists tr. split; [reflexivity|exact Hrep].
  - destruct (bind_b_complete V tr g t ty g1 Hrep Hhead) as [tr1 [Hcheck1 Hrep1]].
    destruct (IH tr1 Hrep1) as [tr2 [Hcheck2 Hrep2]].
    exists tr2. split; [cbn [bind_list_b]; rewrite Hcheck1; exact Hcheck2|exact Hrep2].
Qed.

(** Successful result binding constructs an agreeing context. *)
Lemma bind_result_b_sound : forall V tr g out res tr', (forall x, trie_get x tr = g x) ->
  @bind_result_b V tr out res = Some tr' ->
  exists g', binds_result g out res g' /\ (forall x, trie_get x tr' = g' x).
Proof.
  intros V.
  intros tr g out [t|] tr' Hrep Hcheck; destruct out;
    cbn [bind_result_b binds_result out_sort] in *; try discriminate.
  - eapply (bind_b_sound V); eauto.
  - eapply (bind_b_sound V); eauto.
  - inversion Hcheck; subst tr'. exists g. split; [reflexivity|exact Hrep].
Qed.

(** Declarative result binding is accepted by an agreeing trie. *)
Lemma bind_result_b_complete : forall V tr g out res g', (forall x, trie_get x tr = g x) ->
  @binds_result V g out res g' ->
  exists tr', bind_result_b tr out res = Some tr' /\ (forall x, trie_get x tr' = g' x).
Proof.
  intros V.
  intros tr g out [t|] g' Hrep Hb; destruct out;
    cbn [bind_result_b binds_result out_sort] in *; try contradiction.
  - eapply (bind_b_complete V); eauto.
  - eapply (bind_b_complete V); eauto.
  - subst g'. exists tr. split; [reflexivity|exact Hrep].
Qed.

(** The declaration trie preserves the first declaration of every function name. *)
Lemma decl_table_lookup : forall ds f ss out,
  trie_get f (decl_table ds) = Some (ss, out) <->
  lookup_sorts ds f = Some ss /\ lookup_kind ds f = Some out.
Proof.
  induction ds as [|d ds IH]; intros f ss out; cbn [decl_table lookup_sorts lookup_kind].
  - rewrite PTrie.get_empty. split; [discriminate|intros [H _]; discriminate].
  - destruct (Pos.eqb (name d) f) eqn:Hname.
    + apply Pos.eqb_eq in Hname. subst f. rewrite PTrie.get_set_same.
      split; [intro H; inversion H; subst; split; reflexivity|intros [Hss Hout]; congruence].
    + rewrite PTrie.get_set_other.
      * apply IH.
      * apply Pos.eqb_neq in Hname. congruence.
Qed.

(** Successful query binding constructs a declarative context agreeing with the final trie. *)
Lemma bind_query_b_sound : forall V ds q tr g tr', (forall x, trie_get x tr = g x) ->
  @bind_query_b V (decl_table ds) tr q = Some tr' ->
  exists g', query_ok (lookup_sorts ds) (lookup_kind ds) g q g' /\
    (forall x, trie_get x tr' = g' x).
Proof.
  intros V ds. induction q as [|a q IH]; intros tr g tr' Hrep Hcheck;
    cbn [bind_query_b] in Hcheck.
  - inversion Hcheck; subst tr'. exists g. split; [constructor|exact Hrep].
  - destruct a as [f args res | op args res].
    + destruct (trie_get f (decl_table ds)) as [[ss out]|] eqn:Hlookup;
        [|discriminate].
      destruct (reads_b ss out) eqn:Hreads; [|discriminate].
      apply reads_b_spec in Hreads.
      destruct (bind_list_b tr args ss) as [tr1|] eqn:Hargs; [|discriminate].
      destruct (bind_result_b tr1 out res) as [tr2|] eqn:Hres; [|discriminate].
      destruct (proj1 (decl_table_lookup ds f ss out) Hlookup) as [Hss Hout].
      destruct (bind_list_b_sound V args ss tr g tr1 Hrep Hargs) as [g1 [Hb Hrep1]].
      destruct (bind_result_b_sound V tr1 g1 out res tr2 Hrep1 Hres) as [g2 [Hr Hrep2]].
      destruct (IH tr2 g2 tr' Hrep2 Hcheck) as [g' [Hq Hrep']].
      exists g'. split; [econstructor; eauto|exact Hrep'].
    + destruct (has_vals_b tr args && has_b tr res SVal) eqn:Hargs; [|discriminate].
      apply andb_true_iff in Hargs. destruct Hargs as [Hargs Hres].
      apply (has_vals_b_spec V tr g args Hrep) in Hargs.
      apply (has_b_spec V tr g res SVal Hrep) in Hres.
      destruct (IH tr g tr' Hrep Hcheck) as [g' [Hq Hrep']].
      exists g'. split; [econstructor; eauto|exact Hrep'].
Qed.

(** A declarative query is accepted by a trie agreeing with its initial context. *)
Lemma bind_query_b_complete : forall V ds tr g q g', (forall x, trie_get x tr = g x) ->
  @query_ok V (lookup_sorts ds) (lookup_kind ds) g q g' ->
  exists tr', bind_query_b (decl_table ds) tr q = Some tr' /\
    (forall x, trie_get x tr' = g' x).
Proof.
  intros V ds tr g q g' Hrep Hq. revert tr Hrep.
  induction Hq as
    [g | g g1 g2 g3 f args res ss out rest Hss Hout Hreads Hargs Hres Hrest IH
       | g g1 op args res rest Hargs Hres Hrest IH]; intros tr Hrep.
  - exists tr. split; [reflexivity|exact Hrep].
  - destruct (bind_list_b_complete V tr g args ss g1 Hrep Hargs) as [tr1 [Hb Hrep1]].
    destruct (bind_result_b_complete V tr1 g1 out res g2 Hrep1 Hres) as [tr2 [Hr Hrep2]].
    destruct (IH tr2 Hrep2) as [tr3 [Hq Hrep3]]. exists tr3. split; [|exact Hrep3].
    cbn [bind_query_b].
    rewrite (proj2 (decl_table_lookup ds f ss out) (conj Hss Hout)),
      (proj2 (reads_b_spec ss out) Hreads), Hb, Hr.
    exact Hq.
  - destruct (IH tr Hrep) as [tr' [Hq Hrep']]. exists tr'. split; [|exact Hrep'].
    cbn [bind_query_b]. rewrite (proj2 (has_vals_b_spec V tr g args Hrep) Hargs),
      (proj2 (has_b_spec V tr g res SVal Hrep) Hres). exact Hq.
Qed.
