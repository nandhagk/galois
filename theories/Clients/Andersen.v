(** * Inclusion-based pointer analysis driver

    This driver compiles source constraints and queries their least inclusion solution.
    For example, an address constraint seeds a row used by the first inclusion rule.
    Builds on: AndersenSig and the relational database and run interfaces. *)

From Stdlib Require Import List PArith NArith Bool Lia Arith.
From Argent Require Import Time Tactics Std.
From Galois.Base Require Import Trie.
From Galois.Egglog Require Import Syntax Model Sorts ValueSig IndexSig JoinSig DatabaseSig RunSig.
From Galois.Clients Require Import AndersenSig.
Import List.ListNotations.

(** The inductive inclusion relation contains the seeds and obeys all source constraints. *)
Lemma pointer_source_closed : forall q, pointer_closed q (may_points q).
Proof.
  intro q; unfold pointer_closed; repeat split.
  - intros x a Hinitial; apply May_initial; exact Hinitial.
  - intros x a Haddr; apply May_addr; exact Haddr.
  - intros x y a Hcopy Hpoints; eapply May_copy; eassumption.
  - intros x y location a Hload Hlocation Hpoints; eapply May_load; eassumption.
  - intros x y location a Hstore Hlocation Hpoints; eapply May_store; eassumption.
Qed.

(** Induction over source derivations gives their least closed relation. *)
Lemma pointer_source_least : forall q r, pointer_closed q r ->
  forall x a, may_points q x a -> r x a.
Proof.
  intros q r [Hinitial [Haddr [Hcopy [Hload Hstore]]]] x a Hpoints.
  induction Hpoints; eauto.
Qed.

(** Updating a single pointer preserves coverage when its new target is covered. *)
Lemma pointer_set_covered : forall r memory x a, memory_covered r memory -> r x a ->
  memory_covered r (PTrieCode.set x a memory).
Proof.
  intros r memory x a Hcovered Hnew y b Hget.
  destruct (Pos.eq_dec y x) as [Heq | Hneq].
  - subst y; rewrite PTrie.get_set_same in Hget; inversion Hget; subst b; exact Hnew.
  - rewrite PTrie.get_set_other in Hget by exact Hneq; apply Hcovered; exact Hget.
Qed.

(** Each concrete instruction preserves any source-closed covering relation. *)
Lemma pointer_step_covered : forall q r instruction before after,
  pointer_closed q r -> In instruction (constraints q) -> memory_covered r before ->
  pointer_exec instruction before = Some after -> memory_covered r after.
Proof.
  intros q r instruction before after [Hinitial [Haddr [Hcopy [Hload Hstore]]]]
    Hin Hcovered Hexec.
  destruct instruction as [x a | x y | x y | x y]; cbn [pointer_exec] in Hexec.
  - inversion Hexec; subst after; apply pointer_set_covered; [exact Hcovered |].
    apply Haddr; exact Hin.
  - destruct (trie_get y before) as [a |] eqn:Hy; [|discriminate].
    inversion Hexec; subst after; apply pointer_set_covered; [exact Hcovered |].
    eapply Hcopy; [exact Hin | apply Hcovered; exact Hy].
  - destruct (trie_get y before) as [location |] eqn:Hy; [|discriminate].
    destruct (trie_get location before) as [a |] eqn:Hlocation; [|discriminate].
    inversion Hexec; subst after; apply pointer_set_covered; [exact Hcovered |].
    eapply Hload; [exact Hin | apply Hcovered; exact Hy | apply Hcovered; exact Hlocation].
  - destruct (trie_get x before) as [location |] eqn:Hx; [|discriminate].
    destruct (trie_get y before) as [a |] eqn:Hy; [|discriminate].
    inversion Hexec; subst after; apply pointer_set_covered; [exact Hcovered |].
    eapply Hstore; [exact Hin | apply Hcovered; exact Hx | apply Hcovered; exact Hy].
Qed.

(** A relation atom reads the two values named by its source constraint. *)
Lemma andersen_model_pair : forall prim q rho f u v,
  program_kind andersen_program f = Some ORel ->
  model_atom prim (andersen_model q) (program_kind andersen_program) rho
    (Fun positive f [Var u; Var v] None) ->
  exists x y, rho u = Some (inr x) /\ rho v = Some (inr y) /\ pointer_relation q f x y.
Proof.
  intros prim q rho f u v Hkind [k [Hterms Hrelation]].
  rewrite Hkind in Hrelation; cbn [andersen_model rel] in Hrelation.
  destruct Hrelation as [x [y [Hk Hrelation]]]; subst k.
  inversion Hterms as [|term terms value values Hu Htail]; subst.
  inversion Htail as [|term terms value values Hv Hnil]; subst.
  exists x, y; exact (conj Hu (conj Hv Hrelation)).
Qed.

(** A justified source pointer satisfies the generated points-to action. *)
Lemma andersen_model_put : forall prim q rho u v x a,
  rho u = Some (inr x) -> rho v = Some (inr a) -> may_points q x a ->
  model_actions prim (andersen_model q) (program_kind andersen_program) rho
    [Put 5 [Var u; Var v] None].
Proof.
  intros prim q rho u v x a Hx Ha Hpoints.
  exists [inr x; inr a]; split.
  - constructor; [exact Hx | constructor; [exact Ha | constructor]].
  - split; [|exact I].
    exists x, a; split; [reflexivity |].
    unfold pointer_relation; right; right; right; right; auto.
Qed.

(** Each fixed inclusion rule implements the matching source closure constructor. *)
Lemma andersen_rule_valid : forall prim q r rho,
  In r (rules positive andersen_program) ->
  Forall (model_atom prim (andersen_model q) (program_kind andersen_program) rho)
    (query positive r) ->
  model_actions prim (andersen_model q) (program_kind andersen_program) rho
    (actions positive r).
Proof.
  intros prim q r rho Hin Hquery.
  destruct Hin as [Hr | [Hr | [Hr | [Hr | Hnone]]]]; [subst r | subst r | subst r | subst r |].
  - destruct (andersen_model_pair prim q rho 1 1 2 eq_refl (Forall_inv Hquery))
      as [x [a [Hx [Ha Hsource]]]].
    apply (andersen_model_put prim q rho 1 2 x a Hx Ha).
    apply May_addr; unfold pointer_relation in Hsource; intuition discriminate.
  - pose proof (Forall_inv Hquery) as Hcopy.
    pose proof (Forall_inv (Forall_inv_tail Hquery)) as Hpoints.
    destruct (andersen_model_pair prim q rho 2 1 2 eq_refl Hcopy)
      as [x [y [Hx [Hy Hsource]]]].
    destruct (andersen_model_pair prim q rho 5 2 3 eq_refl Hpoints)
      as [y' [a [Hy' [Ha Htarget]]]].
    assert (Heq : y' = y) by congruence; subst y'.
    apply (andersen_model_put prim q rho 1 3 x a Hx Ha).
    eapply May_copy with (y := y).
    + unfold pointer_relation in Hsource; intuition discriminate.
    + unfold pointer_relation in Htarget; intuition discriminate.
  - pose proof (Forall_inv Hquery) as Hload.
    pose proof (Forall_inv (Forall_inv_tail Hquery)) as Hlocatom.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail Hquery))) as Hpoints.
    destruct (andersen_model_pair prim q rho 3 1 2 eq_refl Hload)
      as [x [y [Hx [Hy Hsource]]]].
    destruct (andersen_model_pair prim q rho 5 2 3 eq_refl Hlocatom)
      as [y' [location [Hy' [Hlocation Hfirst]]]].
    destruct (andersen_model_pair prim q rho 5 3 4 eq_refl Hpoints)
      as [location' [a [Hlocation' [Ha Hsecond]]]].
    assert (Hy_eq : y' = y) by congruence; subst y'.
    assert (Hl_eq : location' = location) by congruence; subst location'.
    apply (andersen_model_put prim q rho 1 4 x a Hx Ha).
    eapply May_load with (y := y) (location := location).
    + unfold pointer_relation in Hsource; intuition discriminate.
    + unfold pointer_relation in Hfirst; intuition discriminate.
    + unfold pointer_relation in Hsecond; intuition discriminate.
  - pose proof (Forall_inv Hquery) as Hstore.
    pose proof (Forall_inv (Forall_inv_tail Hquery)) as Hlocatom.
    pose proof (Forall_inv (Forall_inv_tail (Forall_inv_tail Hquery))) as Hpoints.
    destruct (andersen_model_pair prim q rho 4 1 2 eq_refl Hstore)
      as [x [y [Hx [Hy Hsource]]]].
    destruct (andersen_model_pair prim q rho 5 1 3 eq_refl Hlocatom)
      as [x' [location [Hx' [Hlocation Hfirst]]]].
    destruct (andersen_model_pair prim q rho 5 2 4 eq_refl Hpoints)
      as [y' [a [Hy' [Ha Hsecond]]]].
    assert (Hx_eq : x' = x) by congruence; subst x'.
    assert (Hy_eq : y' = y) by congruence; subst y'.
    apply (andersen_model_put prim q rho 3 4 location a Hlocation Ha).
    eapply May_store with (x := x) (y := y).
    + unfold pointer_relation in Hsource; intuition discriminate.
    + unfold pointer_relation in Hfirst; intuition discriminate.
    + unfold pointer_relation in Hsecond; intuition discriminate.
  - contradiction.
Qed.

(** Evaluating the same list of terms twice yields the same list of cells. *)
Lemma pointer_terms_unique : forall (rho : env (V := positive)) ts first second,
  terms_value rho ts first -> terms_value rho ts second -> first = second.
Proof.
  intros rho ts first second Hfirst; revert second.
  induction Hfirst as [|t c ts cs Hvalue Htail IH]; intros second Hsecond.
  - inversion Hsecond; reflexivity.
  - inversion Hsecond as [|t' c' ts' cs' Hvalue' Htail']; subst.
    f_equal.
    + destruct t; cbn [term_value] in Hvalue, Hvalue'; congruence.
    + apply IH; exact Htail'.
Qed.

(** A list of value cells determines its underlying values uniquely. *)
Lemma pointer_values_unique : forall (cells : list (cell positive)) first second,
  values cells first -> values cells second -> first = second.
Proof.
  intros cells first second Hfirst; revert second.
  induction Hfirst as [|c v cells vals Hvalue Htail IH]; intros second Hsecond.
  - inversion Hsecond; reflexivity.
  - inversion Hsecond as [|c' v' cells' vals' Hvalue' Htail']; subst.
    f_equal; [congruence | apply IH; exact Htail'].
Qed.

(** A derivable action output occurs in every output-free view where the actions are present. *)
Lemma pointer_action_present : forall prim merge (w : view (V := positive)),
  (forall f key output, row w f key output -> output = None) ->
  forall rho acts f key, derivation_action prim rho acts f key ->
    present prim merge w rho acts -> row w f key None.
Proof.
  intros prim merge w Houtputs rho acts f key Hderive.
  induction Hderive as
    [rho f args key rest Hterms |
     rho f args input rest g key Hterms Hderive IH |
     rho x p args key vals value rest f output Hterms Hvalues Hprim Hderive IH];
    intro Hpresent.
  - destruct Hpresent as [key' [output [Hterms' [Hrow Hrest]]]].
    pose proof (pointer_terms_unique rho args key key' Hterms Hterms') as Hkey; subst key'.
    rewrite (Houtputs f key output Hrow) in Hrow; exact Hrow.
  - destruct Hpresent as [key' [output [Hterms' [Hrow [Houtput Hrest]]]]]; apply IH; exact Hrest.
  - destruct Hpresent as [key' [vals' [Hterms' [Hvalues' Hrest]]]].
    pose proof (pointer_terms_unique rho args key key' Hterms Hterms') as Hkey; subst key'.
    pose proof (pointer_values_unique key vals vals' Hvalues Hvalues') as Hvals; subst vals'.
    rewrite Hprim in Hrest; apply IH; exact Hrest.
Qed.

Scheme pointer_derives_ind := Induction for derives Sort Prop
with pointer_body_ind := Induction for derivation_body Sort Prop.

(** Derivations belong to every output-free closed extension of their seed view. *)
Lemma pointer_derives_closed : forall prim merge (p : program positive) initial final,
  closed prim merge p final ->
  (forall f key output, row initial f key output -> row final f key output) ->
  (forall f key output, row final f key output -> output = None) ->
  forall f key, derives prim p initial f key -> row final f key None.
Proof.
  intros prim merge p initial final Hclosed Hinclude Houtputs.
  refine (@pointer_derives_ind positive prim p initial
    (fun f key _ => row final f key None)
    (fun rho body _ => matches prim final body rho) _ _ _ _ _).
  - intros f key Hrow; apply Hinclude; exact Hrow.
  - intros r rho f key Hin Hbody IHbody Haction.
    eapply pointer_action_present; [exact Houtputs | exact Haction |].
    apply Hclosed; [exact Hin | exact IHbody].
  - intro rho; constructor.
  - intros rho f args key rest Hterms Hderive IHderive Hbody IHbody.
    constructor; [exists key, None; split; [exact Hterms | split; [exact I | exact IHderive]] |].
    exact IHbody.
  - intros rho p' args result key vals value rest Hterms Hvalues Hprim Hresult Hbody IHbody.
    constructor; [exists key, vals, value; auto | exact IHbody].
Qed.

(** A binary relation row satisfies the corresponding variable-only query atom. *)
Lemma pointer_atom_row : forall prim w rho f u v x y,
  rho u = Some (Val x) -> rho v = Some (Val y) -> row w f [Val x; Val y] None ->
  atom_holds prim w rho (Fun positive f [Var u; Var v] None).
Proof.
  intros prim w rho f u v x y Hx Hy Hrow; exists [Val x; Val y], None; split.
  - constructor; [exact Hx | constructor; [exact Hy | constructor]].
  - split; [exact I | exact Hrow].
Qed.

(** A present relational action gives its precise row when that relation has no outputs. *)
Lemma pointer_present_row : forall prim merge (w : view (V := positive)) rho u v x a,
  rho u = Some (Val x) -> rho v = Some (Val a) ->
  (forall key output, row w 5 key output -> output = None) ->
  present prim merge w rho [Put 5 [Var u; Var v] None] -> row w 5 [Val x; Val a] None.
Proof.
  intros prim merge w rho u v x a Hx Ha Houtputs [key [output [Hterms [Hrow Hrest]]]].
  assert (Hkey : key = [Val x; Val a]).
  { eapply pointer_terms_unique; [exact Hterms |].
    constructor; [exact Hx | constructor; [exact Ha | constructor]]. }
  subst key; rewrite (Houtputs [Val x; Val a] output Hrow) in Hrow; exact Hrow.
Qed.

(** Closure of the address rule creates its points-to row. *)
Lemma pointer_closed_addr : forall prim merge w x a,
  closed prim merge andersen_program w ->
  (forall key output, row w 5 key output -> output = None) ->
  row w 1 [Val x; Val a] None -> row w 5 [Val x; Val a] None.
Proof.
  intros prim merge w x a Hclosed Houtputs Haddr.
  set (rho := binding_env [1%positive; 2%positive] [Val x; Val a]).
  apply (pointer_present_row prim merge w rho 1 2 x a); try reflexivity; [exact Houtputs |].
  apply (Hclosed (Rule positive [Fun positive 1 [Var 1; Var 2] None]
    [Put 5 [Var 1; Var 2] None]) rho).
  - left; reflexivity.
  - constructor; [eapply pointer_atom_row; [reflexivity | reflexivity | exact Haddr] | constructor].
Qed.

(** Closure of the copy rule propagates an existing pointee. *)
Lemma pointer_closed_copy : forall prim merge w x y a,
  closed prim merge andersen_program w ->
  (forall key output, row w 5 key output -> output = None) ->
  row w 2 [Val x; Val y] None -> row w 5 [Val y; Val a] None ->
  row w 5 [Val x; Val a] None.
Proof.
  intros prim merge w x y a Hclosed Houtputs Hcopy Hpoints.
  set (rho := binding_env [1%positive; 2%positive; 3%positive] [Val x; Val y; Val a]).
  apply (pointer_present_row prim merge w rho 1 3 x a); try reflexivity; [exact Houtputs |].
  apply (Hclosed (Rule positive [Fun positive 2 [Var 1; Var 2] None;
    Fun positive 5 [Var 2; Var 3] None] [Put 5 [Var 1; Var 3] None]) rho).
  - right; left; reflexivity.
  - constructor; [eapply pointer_atom_row; [reflexivity | reflexivity | exact Hcopy] |].
    constructor; [eapply pointer_atom_row; [reflexivity | reflexivity | exact Hpoints] | constructor].
Qed.

(** Closure of the load rule follows the two source pointer edges. *)
Lemma pointer_closed_load : forall prim merge w x y location a,
  closed prim merge andersen_program w ->
  (forall key output, row w 5 key output -> output = None) ->
  row w 3 [Val x; Val y] None -> row w 5 [Val y; Val location] None ->
  row w 5 [Val location; Val a] None -> row w 5 [Val x; Val a] None.
Proof.
  intros prim merge w x y location a Hclosed Houtputs Hload Hlocation Hpoints.
  set (rho := binding_env [1%positive; 2%positive; 3%positive; 4%positive]
    [Val x; Val y; Val location; Val a]).
  apply (pointer_present_row prim merge w rho 1 4 x a); try reflexivity; [exact Houtputs |].
  apply (Hclosed (Rule positive [Fun positive 3 [Var 1; Var 2] None;
    Fun positive 5 [Var 2; Var 3] None; Fun positive 5 [Var 3; Var 4] None]
    [Put 5 [Var 1; Var 4] None]) rho).
  - right; right; left; reflexivity.
  - constructor; [eapply pointer_atom_row; [reflexivity | reflexivity | exact Hload] |].
    constructor; [eapply pointer_atom_row; [reflexivity | reflexivity | exact Hlocation] |].
    constructor; [eapply pointer_atom_row; [reflexivity | reflexivity | exact Hpoints] | constructor].
Qed.

(** Closure of the store rule adds the stored pointee at the destination location. *)
Lemma pointer_closed_store : forall prim merge w x y location a,
  closed prim merge andersen_program w ->
  (forall key output, row w 5 key output -> output = None) ->
  row w 4 [Val x; Val y] None -> row w 5 [Val x; Val location] None ->
  row w 5 [Val y; Val a] None -> row w 5 [Val location; Val a] None.
Proof.
  intros prim merge w x y location a Hclosed Houtputs Hstore Hlocation Hpoints.
  set (rho := binding_env [1%positive; 2%positive; 3%positive; 4%positive]
    [Val x; Val y; Val location; Val a]).
  apply (pointer_present_row prim merge w rho 3 4 location a); try reflexivity;
    [exact Houtputs |].
  apply (Hclosed (Rule positive [Fun positive 4 [Var 1; Var 2] None;
    Fun positive 5 [Var 1; Var 3] None; Fun positive 5 [Var 2; Var 4] None]
    [Put 5 [Var 3; Var 4] None]) rho).
  - right; right; right; left; reflexivity.
  - constructor; [eapply pointer_atom_row; [reflexivity | reflexivity | exact Hstore] |].
    constructor; [eapply pointer_atom_row; [reflexivity | reflexivity | exact Hlocation] |].
    constructor; [eapply pointer_atom_row; [reflexivity | reflexivity | exact Hpoints] | constructor].
Qed.

(** An output-free closed extension contains every source inclusion derivation. *)
Lemma pointer_closed_source : forall prim merge q w,
  closed prim merge andersen_program w ->
  (forall f key output, pointer_seed_row q f key output -> row w f key output) ->
  (forall key output, row w 5 key output -> output = None) ->
  forall x a, may_points q x a -> row w 5 [Val x; Val a] None.
Proof.
  intros prim merge q w Hclosed Hseed Houtputs x a Hpoints.
  induction Hpoints as [x a Hin | x a Hin | x y a Hin Hpoints IH |
    x y location a Hin Hlocation IHlocation Hpoints IHpoints |
    x y location a Hin Hlocation IHlocation Hpoints IHpoints].
  - apply Hseed; split; [reflexivity | exists x, a; split; [reflexivity |]].
    right; right; right; right; auto.
  - eapply pointer_closed_addr; [exact Hclosed | exact Houtputs |].
    apply Hseed; split; [reflexivity | exists x, a; split; [reflexivity | left; auto]].
  - eapply pointer_closed_copy; [exact Hclosed | exact Houtputs | | exact IH].
    apply Hseed; split; [reflexivity | exists x, y; split; [reflexivity | right; left; auto]].
  - eapply pointer_closed_load;
      [exact Hclosed | exact Houtputs | | exact IHlocation | exact IHpoints].
    apply Hseed; split; [reflexivity | exists x, y; split; [reflexivity | right; right; left; auto]].
  - eapply pointer_closed_store;
      [exact Hclosed | exact Houtputs | | exact IHlocation | exact IHpoints].
    apply Hseed; split; [reflexivity | exists x, y; split; [reflexivity |]].
    right; right; right; left; auto.
Qed.

(** Every declared function of the inclusion program is a relation. *)
Lemma andersen_kind_relation : forall f output,
  program_kind andersen_program f = Some output -> output = ORel.
Proof.
  intros f output Hkind; unfold program_kind, andersen_program in Hkind.
  cbn [decls lookup_kind] in Hkind.
  repeat match type of Hkind with context [if ?b then _ else _] => destruct b end;
    inversion Hkind; reflexivity.
Qed.

(** This source needs the single points-to consequence from its address constraint. *)
Definition pointer_defect_input : pointer_input := PointerInput [Addr 1 2] [].

(** This unsorted view replaces all points-to relation outputs with a value output. *)
Definition pointer_defect_view : view (V := positive) :=
  View (fun f _ output => output = Some (Val 1%positive) \/
      (f <> 5%positive /\ output = None))
    (fun i j => i = j) (fun _ => Some ORel).

(** A relation-5 query cannot match the deliberately malformed value-output rows. *)
Lemma pointer_defect_no_match : forall prim rho u v,
  ~ atom_holds prim pointer_defect_view rho (Fun positive 5 [Var u; Var v] None).
Proof.
  intros prim rho u v [key [output [Hterms [Hresult Hrow]]]].
  destruct output as [c |]; [contradiction |].
  cbn [pointer_defect_view row] in Hrow; intuition discriminate.
Qed.

(** Presence accepts the malformed address consequence, while other rules cannot match. *)
Lemma pointer_defect_closed : forall prim merge,
  closed prim merge andersen_program pointer_defect_view.
Proof.
  intros prim merge r rho Hin Hquery.
  destruct Hin as [Hr | [Hr | [Hr | [Hr | Hnone]]]];
    [subst r | subst r | subst r | subst r |].
  - destruct (Forall_inv Hquery) as [key [output [Hterms [Hresult Hrow]]]].
    exists key, (Some (Val 1%positive)); split; [exact Hterms |].
    split; [left; reflexivity | split; exact I].
  - exfalso; eapply pointer_defect_no_match; exact (Forall_inv (Forall_inv_tail Hquery)).
  - exfalso; eapply pointer_defect_no_match; exact (Forall_inv (Forall_inv_tail Hquery)).
  - exfalso; eapply pointer_defect_no_match; exact (Forall_inv (Forall_inv_tail Hquery)).
  - contradiction.
Qed.

(** The frozen arbitrary-view plan fails because closure does not enforce output kinds. *)
Lemma pointer_closed_source_counterexample : forall prim merge,
  closed prim merge andersen_program pointer_defect_view /\
  (forall f key output, pointer_seed_row pointer_defect_input f key output ->
    row pointer_defect_view f key output) /\
  may_points pointer_defect_input 1 2 /\
  ~ row pointer_defect_view 5 [Val 1%positive; Val 2%positive] None.
Proof.
  intros prim merge; split; [apply pointer_defect_closed | split].
  - intros f key output [Ho [x [y [Hkey Hsource]]]]; subst output.
    destruct Hsource as [[Hf Hin] | [[Hf Hin] | [[Hf Hin] | [[Hf Hin] | [Hf Hin]]]]];
      subst f; try (right; split; [discriminate | reflexivity]).
    exact (False_rect _ Hin).
  - split.
    + apply May_addr; left; reflexivity.
    + cbn [pointer_defect_view row]; intuition discriminate.
Qed.

(** Each source instruction is stored in its own binary relation. *)
Definition pointer_constraint_entry (instruction : pointer_constraint) :
    positive * (positive * positive) :=
  match instruction with
  | Addr x y => (1%positive, (x, y))
  | Copy x y => (2%positive, (x, y))
  | Load x y => (3%positive, (x, y))
  | Store x y => (4%positive, (x, y))
  end.
TimeFun pointer_constraint_entry.

(** Initial pointers use the relation chosen by the analysis client. *)
Definition pointer_seed_entries (initial_relation : positive) (q : pointer_input) :
    list (positive * (positive * positive)) :=
  match q with
  | PointerInput instructions initial =>
    map pointer_constraint_entry instructions ++
      map (fun pointer => (initial_relation, pointer)) initial
  end.
TimeFun pointer_seed_entries.

(** Each source item contributes exactly one seed entry. *)
Lemma pointer_seed_entries_length : forall initial_relation q,
  length (pointer_seed_entries initial_relation q) =
    length (constraints q) + length (initial_pointers q).
Proof.
  intros initial_relation [instructions initial]; cbn [pointer_seed_entries constraints initial_pointers].
  rewrite length_app, !length_map; reflexivity.
Qed.

(** Encoding and concatenating the source seed entries takes linear list work. *)
Lemma pointer_seed_entries_time : forall initial_relation q,
  (T_pointer_seed_entries initial_relation q <=
    16 * N.of_nat (length (constraints q) + length (initial_pointers q) + 1))%N.
Proof.
  intros initial_relation [instructions initial].
  assert (Hconstraint : forall c, (T_pointer_constraint_entry c <= 1)%N).
  { intro c; destruct c; reflexivity. }
  pose proof (ListDef.T_map_le pointer_constraint_entry T_pointer_constraint_entry 1 instructions
    Hconstraint) as Hmap.
  pose proof (ListDef.T_map_le (fun pointer : positive * positive => (initial_relation, pointer))
    (fun _ => 1%N) 1 initial ltac:(intros; reflexivity)) as Hinitial.
  pose proof (Datatypes.T_app_le (map pointer_constraint_entry instructions)
    (map (fun pointer => (initial_relation, pointer)) initial)) as Happ.
  rewrite length_map in Happ.
  time_unfold T_pointer_seed_entries; time_simpl.
  cbn [constraints initial_pointers]; rewrite !Nat2N.inj_add.
  unfold T_pointer_constraint_entry in Hmap; nia.
Qed.

(** Reading a plan's slot layout is one record elimination. *)
Definition pointer_plan_slots {V} (plan : compiled V) : list (positive * list nat) :=
  match plan with Compiled _ layout _ _ => layout end.
TimeFun pointer_plan_slots.

(** Entry membership is exactly a source constraint or a listed initial pointer. *)
Lemma pointer_seed_entries_spec : forall initial_relation q f x y,
  In (f, (x, y)) (pointer_seed_entries initial_relation q) <->
    (f = 1%positive /\ In (Addr x y) (constraints q)) \/
    (f = 2%positive /\ In (Copy x y) (constraints q)) \/
    (f = 3%positive /\ In (Load x y) (constraints q)) \/
    (f = 4%positive /\ In (Store x y) (constraints q)) \/
    (f = initial_relation /\ In (x, y) (initial_pointers q)).
Proof.
  intros initial_relation [instructions initial] f x y.
  cbn [pointer_seed_entries constraints initial_pointers]; rewrite in_app_iff; split.
  - intros [Hinstruction | Hinitial].
    + apply in_map_iff in Hinstruction; destruct Hinstruction as [instruction [Heq Hin]].
      destruct instruction; cbn [pointer_constraint_entry] in Heq; inversion Heq; subst;
        tauto.
    + apply in_map_iff in Hinitial; destruct Hinitial as [[a b] [Heq Hin]].
      inversion Heq; subst; tauto.
  - intros [[Hf Hin] | [[Hf Hin] | [[Hf Hin] | [[Hf Hin] | [Hf Hin]]]]]; subst f.
    + left; apply in_map_iff; exists (Addr x y); auto.
    + left; apply in_map_iff; exists (Copy x y); auto.
    + left; apply in_map_iff; exists (Load x y); auto.
    + left; apply in_map_iff; exists (Store x y); auto.
    + right; apply in_map_iff; exists (x, y); auto.
Qed.

(** A successful declaration search agrees with both declaration lookup functions. *)
Lemma pointer_declaration_lookup : forall ds f d,
  find (fun entry => Pos.eqb (name entry) f) ds = Some d ->
  lookup_kind ds f = Some (out d) /\ lookup_sorts ds f = Some (arg_sorts d).
Proof.
  induction ds as [|entry rest IH]; intros f d Hfind; [discriminate |].
  cbn [find lookup_kind lookup_sorts] in *.
  destruct (Pos.eqb (name entry) f) eqn:Hname.
  - inversion Hfind; subst d; split; reflexivity.
  - apply IH; exact Hfind.
Qed.

(** Seeding preserves a relational database and records exactly the inserted value pairs. *)
Module PointerSeedFacts (V : VALUE with Definition t := positive)
    (I : INDEX V) (J : JOIN V I) (D : DATABASE V I) (R : RUN V I J D).
  Definition put_entry (db : D.t) (entry : positive * (positive * positive)) : D.t :=
    D.put (fst entry) [Val (fst (snd entry)); Val (snd (snd entry))] None db.
  Definition entry_ok (p : program V.t) (entry : positive * (positive * positive)) :=
    program_kind p (fst entry) = Some ORel /\
    program_sorts p (fst entry) = Some [SVal; SVal].
  Definition entry_row (entry : positive * (positive * positive)) f k
      (o : option (cell V.t)) :=
    f = fst entry /\ k = [Val (fst (snd entry)); Val (snd (snd entry))] /\ o = None.
  Definition invariant (p : program V.t) (db : D.t) :=
    D.wf db /\ R.loaded p (R.plan p) db /\ R.no_ids db.

  (** Every slot of a checked binary relation accepts its two value arguments. *)
  Lemma entry_kind_ok : forall p db entry, R.plans_ok p (R.plan p) ->
    R.loaded p (R.plan p) db -> entry_ok p entry ->
    D.kind_ok db (fst entry) [Val (fst (snd entry)); Val (snd (snd entry))] None.
  Proof.
    intros p db [f [x y]] Hplan [Hkinds [Hslots Hsorted]] [Hkind Hsort].
    cbn [fst snd] in *; split.
    - intros i Hin; cbn [option_list app] in Hin.
      destruct Hin as [Heq | [Heq | Hnone]]; discriminate || contradiction.
    - split.
      + intros perm Hin; rewrite Hslots in Hin.
        destruct (R.check_plan_slots p (R.plan p) f perm Hplan Hin)
          as [d [Hfind [Hdistinct Hbounds]]].
        destruct (pointer_declaration_lookup (decls V.t p) f d Hfind) as [Hout Hargs].
        assert (Hout_eq : out d = ORel) by (unfold program_kind in Hkind; congruence).
        assert (Hargs_eq : arg_sorts d = [SVal; SVal]) by
          (unfold program_sorts in Hsort; congruence).
        rewrite Hout_eq, Hargs_eq in Hbounds; cbn in Hbounds.
        split; [exact Hdistinct | exact Hbounds].
      + rewrite Hkinds, Hkind; exact I.
  Qed.

  (** Inserting a relation row adds that row and preserves every old relation row. *)
  Lemma entry_rows : forall p db entry, R.plans_ok p (R.plan p) ->
    invariant p db -> entry_ok p entry -> forall f k o,
    row (D.view (put_entry db entry)) f k o <-> row (D.view db) f k o \/ entry_row entry f k o.
  Proof.
    intros p db [g [x y]] Hplan [Hwf [Hloaded [Hids Hrows]]] Hentry f k o.
    pose proof (entry_kind_ok p db (g, (x, y)) Hplan Hloaded Hentry) as Hkind.
    assert (Hcombine : D.combine db g (D.old db g [Val x; Val y]) None = None).
    { destruct (D.old db g [Val x; Val y]) as [[c |] |] eqn:Hlookup; [|reflexivity|reflexivity].
      pose proof (proj1 (D.old_row db g [Val x; Val y] (Some c) Hwf) Hlookup) as Hrow.
      destruct (Hrows g [Val x; Val y] (Some c) Hrow) as [Hnone _]; discriminate. }
    unfold put_entry, entry_row; cbn [fst snd].
    rewrite (D.put_rows g [Val x; Val y] None db Hwf Hkind).
    change (((row (D.view db) f k o /\ (f, k) <> (g, [Val x; Val y])) \/
      (f = g /\ k = [Val x; Val y] /\
        D.combine db g (D.old db g [Val x; Val y]) None = o)) <->
      row (D.view db) f k o \/ (f = g /\ k = [Val x; Val y] /\ o = None)).
    rewrite Hcombine; split.
    - intros [[Hrow Hneq] | [Hf [Hk Ho]]]; [left; exact Hrow | right; auto].
    - intros [Hrow | [Hf [Hk Ho]]].
      + destruct (Pos.eq_dec f g) as [Hf | Hf].
        * subst f.
          assert (Hkeys : {k = [Val x; Val y]} + {k <> [Val x; Val y]}).
          { decide equality; decide equality; apply Pos.eq_dec. }
          destruct Hkeys as [Hk | Hk].
          -- right; subst k; repeat split; try reflexivity.
             symmetry; exact (proj1 (Hrows g [Val x; Val y] o Hrow)).
          -- left; split; [exact Hrow | congruence].
        * left; split; [exact Hrow | congruence].
      + right; auto.
  Qed.

  (** Adding a well-sorted relation row preserves the complete seeding invariant. *)
  Lemma entry_invariant : forall p db entry, R.plans_ok p (R.plan p) ->
    invariant p db -> entry_ok p entry -> invariant p (put_entry db entry).
  Proof.
    intros p db entry Hplan Hinv Hentry.
    destruct Hinv as [Hwf [Hloaded Hnoids]].
    destruct Hloaded as [Hkinds [Hslots Hsorted]].
    destruct Hnoids as [Hids Hrows].
    pose proof (entry_kind_ok p db entry Hplan (conj Hkinds (conj Hslots Hsorted)) Hentry)
      as Hkind.
    destruct (D.layout_put (fst entry) [Val (fst (snd entry)); Val (snd (snd entry))]
      None db Hwf) as [Hkind_next [Hslots_next [Hids_next Hpending]]].
    assert (Hrow_spec : forall f k o, row (D.view (put_entry db entry)) f k o <->
      row (D.view db) f k o \/ entry_row entry f k o).
    { apply entry_rows with (p := p).
      - exact Hplan.
      - exact (conj Hwf (conj (conj Hkinds (conj Hslots Hsorted)) (conj Hids Hrows))).
      - exact Hentry. }
    unfold invariant, put_entry; split; [apply D.wf_put; assumption | split].
    - split; [intro f; rewrite Hkind_next; apply Hkinds | split].
      + rewrite Hslots_next; exact Hslots.
      + intros f k o Hrow; apply Hrow_spec in Hrow.
        destruct Hrow as [Hrow | [Hf [Hk Ho]]].
        * unfold row_sorted; rewrite Hkind_next; apply Hsorted; exact Hrow.
        * subst f k o; exists ORel; split; [exact (proj2 Hentry) | split; [|reflexivity]].
          rewrite Hkind_next, Hkinds; exact (proj1 Hentry).
    - split; [rewrite Hids_next; exact Hids |].
      intros f k o Hrow; apply Hrow_spec in Hrow.
      destruct Hrow as [Hrow | [Hf [Hk Ho]]].
      + exact (Hrows f k o Hrow).
      + subst k o; split; [reflexivity |].
        constructor; [eexists; reflexivity | constructor; [eexists; reflexivity | constructor]].
  Qed.

  (** Folding over compatible entries preserves the seeding invariant. *)
  Lemma fold_invariant : forall p entries db, R.plans_ok p (R.plan p) ->
    invariant p db -> Forall (entry_ok p) entries ->
    invariant p (fold_left put_entry entries db).
  Proof.
    intros p entries; induction entries as [|entry rest IH]; intros db Hplan Hinv Hentries.
    - exact Hinv.
    - inversion Hentries as [|e es Hentry Hrest]; subst.
      apply IH; [exact Hplan | eapply entry_invariant; eassumption | exact Hrest].
  Qed.

  (** Folding inserts exactly the listed entries in addition to the initial rows. *)
  Lemma fold_rows : forall p entries db, R.plans_ok p (R.plan p) ->
    invariant p db -> Forall (entry_ok p) entries -> forall f k o,
    row (D.view (fold_left put_entry entries db)) f k o <->
      row (D.view db) f k o \/ exists entry, In entry entries /\ entry_row entry f k o.
  Proof.
    intros p entries; induction entries as [|entry rest IH]; intros db Hplan Hinv Hentries f k o.
    - cbn [fold_left]; split; [auto | intros [Hrow | [e [Hnone _]]]; [exact Hrow | contradiction]].
    - inversion Hentries as [|e es Hentry Hrest]; subst; cbn [fold_left].
      rewrite (IH (put_entry db entry) Hplan
        (entry_invariant p db entry Hplan Hinv Hentry) Hrest f k o).
      rewrite (entry_rows p db entry Hplan Hinv Hentry f k o).
      split.
      + intros [[Hrow | Hnew] | [e [Hin He]]].
        * left; exact Hrow.
        * right; exists entry; split; [left; reflexivity | exact Hnew].
        * right; exists e; split; [right; exact Hin | exact He].
      + intros [Hrow | [e [[Heq | Hin] He]]].
        * left; left; exact Hrow.
        * subst e; left; right; exact He.
        * right; exists e; auto.
  Qed.

  (** Database initialization establishes the empty relational invariant. *)
  Lemma init_invariant : forall p,
    invariant p (D.init (decls V.t p) (Syntax.slots V.t (R.plan p))).
  Proof.
    intro p; split; [apply D.wf_init | split].
    - split.
      + intro f; exact (proj1 (proj2 (proj2
          (D.init_view (decls V.t p) (Syntax.slots V.t (R.plan p)) f [] None 1 1)))).
      + split.
        * exact (proj1 (proj2 (proj2 (proj2
            (D.init_view (decls V.t p) (Syntax.slots V.t (R.plan p)) 1 [] None 1 1))))).
        * intros f k o Hrow.
          apply (proj1 (proj1
            (D.init_view (decls V.t p) (Syntax.slots V.t (R.plan p)) f k o 1 1))) in Hrow.
          contradiction.
    - split.
      + exact (proj1 (proj2 (proj2 (proj2 (proj2
          (D.init_view (decls V.t p) (Syntax.slots V.t (R.plan p)) 1 [] None 1 1)))))).
      + intros f k o Hrow.
        apply (proj1 (proj1
          (D.init_view (decls V.t p) (Syntax.slots V.t (R.plan p)) f k o 1 1))) in Hrow.
        contradiction.
  Qed.

  (** An identifier-free relational database is canonical. *)
  Lemma no_ids_canonical : forall db, R.no_ids db -> D.canonical db.
  Proof.
    intros db [Hids Hrows] f k o Hrow i Hin.
    destruct (Hrows f k o Hrow) as [Ho Hvalues]; subst o.
    cbn [option_list] in Hin; rewrite app_nil_r in Hin.
    apply (proj1 (Forall_forall _ _) Hvalues) in Hin.
    destruct Hin as [v Heq]; discriminate.
  Qed.
End PointerSeedFacts.

(** A fixed plan is charged for each function name and each selected position. *)
Definition pointer_layout_size (sl : list (positive * list nat)) : nat :=
  fold_right (fun s n => Pos.size_nat (fst s) + length (snd s) + 1 + n) 0 sl.

(** The plan-size sum bounds its slot count, tuple lengths and function-name sizes. *)
Lemma pointer_layout_size_bounds : forall sl,
  length sl <= pointer_layout_size sl /\
  fold_right (fun s n => length (snd s) + n) 0 sl <= pointer_layout_size sl /\
  fold_right (fun s n => Pos.size_nat (fst s) + n) 0 sl <= pointer_layout_size sl.
Proof.
  intro sl; induction sl as [|[f perm] rest [Hcount [Hlength Hnames]]].
  - repeat split; reflexivity.
  - unfold pointer_layout_size in *; cbn [length fold_right fst snd] in *.
    split; [|split]; lia.
Qed.

(** A permutation of at most two positions has a fixed preparation budget. *)
Lemma pointer_permutation_work : forall perm, NoDup perm -> Forall (fun i => i < 2) perm ->
  (length perm + 1) * (fold_right Nat.add 0 (map S perm) + length perm + 1) <= 21.
Proof.
  intros perm Hdistinct Hbounds.
  assert (Hlength : length perm <= 2).
  { change (length perm <= length [0; 1]); apply NoDup_incl_length; [exact Hdistinct |].
    intros i Hin; apply (proj1 (Forall_forall _ _) Hbounds) in Hin.
    cbn; lia. }
  assert (Hsum : fold_right Nat.add 0 (map S perm) <= 2 * length perm).
  { clear Hlength Hdistinct.
    induction Hbounds as [|i rest Hi Hrest IH]; cbn [map fold_right length]; lia. }
  nia.
Qed.

(** Preparing binary slots costs at most a fixed multiple of their encoded size. *)
Lemma pointer_layout_work : forall sl,
  Forall (fun s => NoDup (snd s) /\ Forall (fun i => i < 2) (snd s)) sl ->
  layout_work sl <= 21 * pointer_layout_size sl.
Proof.
  intros sl Hslots; induction Hslots as [|[f perm] rest [Hdistinct Hbounds] Hrest IH].
  - reflexivity.
  - pose proof (pointer_permutation_work perm Hdistinct Hbounds) as Hperm.
    unfold layout_work, pointer_layout_size in *; cbn [map fold_right fst snd] in *; nia.
Qed.

Module PointerSeedTime (V : VALUE_T with Definition t := positive)
    (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I) (R : RUN_T V I J D).
  Module Facts := PointerSeedFacts V I J D R.

  (** Checked plans for binary tuples have only permutations of the two positions. *)
  Lemma binary_plan_slots : forall p, R.plans_ok p (R.plan p) ->
    Forall (fun d => length (arg_sorts d) + match out d with ORel => 0 | _ => 1 end <= 2)
      (decls V.t p) ->
    Forall (fun s => NoDup (snd s) /\ Forall (fun i => i < 2) (snd s))
      (Syntax.slots V.t (R.plan p)).
  Proof.
    intros p Hplan Hdecls; apply Forall_forall; intros [f perm] Hin.
    destruct (R.check_plan_slots p (R.plan p) f perm Hplan Hin)
      as [d [Hfind [Hdistinct Hbounds]]].
    split; [exact Hdistinct |].
    apply find_some in Hfind; destruct Hfind as [Hdecl Hname].
    apply (proj1 (Forall_forall _ _) Hdecls) in Hdecl.
    apply Forall_forall; intros i Hin_position.
    apply (proj1 (Forall_forall _ _) Hbounds) in Hin_position; lia.
  Qed.

  (** Initializing a binary fixed program is quadratic in the bounded plan size. *)
  Lemma init_time : forall p K, R.plans_ok p (R.plan p) ->
    Forall (fun d => length (arg_sorts d) + match out d with ORel => 0 | _ => 1 end <= 2)
      (decls V.t p) ->
    length (decls V.t p) <= 8 ->
    fold_right (fun d n => Pos.size_nat (name d) + n) 0 (decls V.t p) <= 32 ->
    (N.of_nat (pointer_layout_size (Syntax.slots V.t (R.plan p))) <= K)%N ->
    (D.T_init (decls V.t p) (Syntax.slots V.t (R.plan p)) <=
      64 * (D.c_db + 1) * (K + 8) * (K + 8))%N.
  Proof.
    intros p K Hplan Hdecls Hcount Hnames Hsize.
    pose proof (D.T_init_le (decls V.t p) (Syntax.slots V.t (R.plan p))) as Hinit.
    pose proof (pointer_layout_size_bounds (Syntax.slots V.t (R.plan p)))
      as [Hslots [Hlengths Hslot_names]].
    pose proof (pointer_layout_work (Syntax.slots V.t (R.plan p))
      (binary_plan_slots p Hplan Hdecls)) as Hwork.
    apply time_of_nat_le in Hcount; apply time_of_nat_le in Hnames.
    apply time_of_nat_le in Hslots; apply time_of_nat_le in Hlengths.
    apply time_of_nat_le in Hslot_names; apply time_of_nat_le in Hwork.
    rewrite ?Nat2N.inj_add, ?Nat2N.inj_mul in *; nia.
  Qed.
(** Scaling a nonnegative amortized credit to a larger positive unit is sound. *)
  Lemma credit_scale : forall (ticks charge before after : N) (u U : nat),
    (1 <= u)%nat -> (u <= U)%nat ->
    (ticks + N.of_nat u * after <= N.of_nat u * (charge + before))%N ->
    (ticks + N.of_nat U * after <= N.of_nat U * (charge + before))%N.
  Proof.
    intros ticks charge before after u U Hpositive Hunit Hcredit.
    assert (Hu : (0 < N.of_nat u)%N) by lia.
    assert (HuU : (N.of_nat u <= N.of_nat U)%N) by lia.
    assert (Hbalance : (after <= charge + before)%N) by nia.
    nia.
  Qed.

  (** Every database spending unit is positive by its manifest definition. *)
  Lemma unit_positive : forall db, (1 <= D.unit db)%nat.
  Proof.
    intro db. unfold D.unit. nia.
  Qed.

  (** A loaded database has at most as many matching slots as the complete plan. *)
  Lemma entry_slots : forall p db f, R.loaded p (R.plan p) db ->
    (D.slots_of db f <= length (Syntax.slots V.t (R.plan p)))%nat.
  Proof.
    intros p db f [_ [Hslots _]]. unfold D.slots_of. rewrite Hslots.
    apply filter_length_le.
  Qed.

  (** The unit of every intermediate seed is bounded by the completed fold's unit. *)
  Lemma fold_unit_mono : forall p entries db,
    R.plans_ok p (R.plan p) -> Facts.invariant p db ->
    Forall (Facts.entry_ok p) entries ->
    (D.unit db <= D.unit (fold_left Facts.put_entry entries db))%nat.
  Proof.
    intros p entries. induction entries as [|entry rest IH]; intros db Hplan Hinv Hentries.
    - reflexivity.
    - inversion Hentries as [|entry' rest' Hentry Hrest]; subst.
      cbn [fold_left]. eapply Nat.le_trans.
      + unfold Facts.put_entry. apply D.unit_mono_put. exact (proj1 Hinv).
      + apply IH; [exact Hplan| |exact Hrest].
        exact (Facts.entry_invariant p db entry Hplan Hinv Hentry).
  Qed.

  (** A binary value-row insertion pays its clock and credit at any final upper unit. *)
  Lemma entry_credit : forall p (T_entry : D.t -> positive * (positive * positive) -> N)
      (K : N) (U : nat) db entry,
    R.plans_ok p (R.plan p) -> Facts.invariant p db -> Facts.entry_ok p entry ->
    (N.of_nat (length (Syntax.slots V.t (R.plan p)) + 1) <= K)%N ->
    (D.unit (Facts.put_entry db entry) <= U)%nat ->
    (T_entry db entry <= D.T_put (fst entry)
      [Val (fst (snd entry)); Val (snd (snd entry))] None db + 32)%N ->
    (T_entry db entry + N.of_nat U * D.potential 0 (Facts.put_entry db entry) <=
      N.of_nat U * ((16 * D.c_db * K + 32) + D.potential 0 db))%N.
  Proof.
    intros p T_entry K U db [f [x y]] Hplan Hinv Hentry HK HU Hclock.
    pose proof (Facts.entry_invariant p db (f, (x, y)) Hplan Hinv Hentry) as Hnext.
    pose proof (Facts.entry_kind_ok p db (f, (x, y)) Hplan
      (proj1 (proj2 Hinv)) Hentry) as Hkind.
    assert (Hids : (D.ids (D.put f [Val x; Val y] None db) <= 0)%N).
    { change (D.ids (Facts.put_entry db (f, (x, y))) <= 0)%N.
      rewrite (proj1 (proj2 (proj2 Hnext))). reflexivity. }
    pose proof (D.T_put_amort 0 f [Val x; Val y] None db (proj1 Hinv)
      (proj1 (proj2 Hkind)) Hids) as Hraw.
    change (D.T_put f [Val x; Val y] None db +
      N.of_nat (D.unit (Facts.put_entry db (f, (x, y)))) *
        D.potential 0 (Facts.put_entry db (f, (x, y))) <=
      N.of_nat (D.unit (Facts.put_entry db (f, (x, y)))) *
        (D.c_db * 16 * N.of_nat (D.slots_of db f + 1) * 1 + D.potential 0 db))%N in Hraw.
    rewrite N.mul_1_r in Hraw.
    pose proof (credit_scale _ _ _ _ _ U
      (unit_positive (Facts.put_entry db (f, (x, y)))) HU Hraw) as Hscaled.
    pose proof (entry_slots p db f (proj1 (proj2 Hinv))) as Hslots.
    assert (HslotN : (N.of_nat (D.slots_of db f + 1) <= K)%N) by lia.
    assert (Hcharge : (D.c_db * 16 * N.of_nat (D.slots_of db f + 1) <=
      16 * D.c_db * K)%N) by nia.
    pose proof (N.mul_le_mono_l _ _ (N.of_nat U) Hcharge) as Hcharged.
    assert (HUpositive : (1 <= N.of_nat U)%N).
    { pose proof (unit_positive (Facts.put_entry db (f, (x, y)))). lia. }
    cbn [fst snd] in Hclock.
    repeat rewrite N.mul_add_distr_l in Hscaled |- *. lia.
  Qed.

  (** A seed fold telescopes potential at one fixed upper bound on its final unit. *)
  Lemma fold_credit : forall p entries
      (T_entry : D.t -> positive * (positive * positive) -> N) (K : N) (U : nat),
    R.plans_ok p (R.plan p) ->
    (N.of_nat (length (Syntax.slots V.t (R.plan p)) + 1) <= K)%N ->
    (forall db entry, (T_entry db entry <= D.T_put (fst entry)
      [Val (fst (snd entry)); Val (snd (snd entry))] None db + 32)%N) ->
    forall db, Facts.invariant p db -> Forall (Facts.entry_ok p) entries ->
    (D.unit (fold_left Facts.put_entry entries db) <= U)%nat ->
    (Std.List.T_fold_left Facts.put_entry T_entry entries db +
      N.of_nat U * D.potential 0 (fold_left Facts.put_entry entries db) <=
      N.of_nat U * ((16 * D.c_db * K + 33) * N.of_nat (length entries) +
        D.potential 0 db) + 1)%N.
  Proof.
    intros p entries T_entry K U Hplan HK Hclock.
    induction entries as [|entry rest IH]; intros db Hinv Hentries Hfinal.
    - time_unfold @Std.List.T_fold_left. cbn [fold_left length]. nia.
    - inversion Hentries as [|entry' rest' Hentry Hrest]; subst.
      pose proof (Facts.entry_invariant p db entry Hplan Hinv Hentry) as Hnext.
      assert (Hnext_unit : (D.unit (Facts.put_entry db entry) <= U)%nat).
      { eapply Nat.le_trans; [apply (fold_unit_mono p rest _ Hplan Hnext Hrest)|].
        exact Hfinal. }
      pose proof (entry_credit p T_entry K U db entry Hplan Hinv Hentry HK Hnext_unit
        (Hclock db entry)) as Hstep.
      specialize (IH (Facts.put_entry db entry) Hnext Hrest Hfinal).
      assert (HUpositive : (1 <= N.of_nat U)%N).
      { pose proof (unit_positive (Facts.put_entry db entry)). lia. }
      time_unfold @Std.List.T_fold_left. cbn [fold_left length].
      rewrite Nat2N.inj_succ.
      set (tail_charge := ((16 * D.c_db * K + 33) * N.of_nat (length rest))%N) in *.
      replace ((16 * D.c_db * K + 33) * N.succ (N.of_nat (length rest)))%N with
        (tail_charge + (16 * D.c_db * K + 33))%N by (unfold tail_charge; nia).
      repeat rewrite N.mul_add_distr_l in Hstep, IH |- *. lia.
  Qed.

  (** Initialization has zero credit, giving a plain bound for the complete seed fold. *)
  Lemma fold_time : forall p entries
      (T_entry : D.t -> positive * (positive * positive) -> N) (K : N),
    R.plans_ok p (R.plan p) ->
    (N.of_nat (length (Syntax.slots V.t (R.plan p)) + 1) <= K)%N ->
    (forall db entry, (T_entry db entry <= D.T_put (fst entry)
      [Val (fst (snd entry)); Val (snd (snd entry))] None db + 32)%N) ->
    Forall (Facts.entry_ok p) entries ->
    let initial := D.init (decls V.t p) (Syntax.slots V.t (R.plan p)) in
    (Std.List.T_fold_left Facts.put_entry T_entry entries initial <=
      N.of_nat (D.unit (fold_left Facts.put_entry entries initial)) *
        (16 * D.c_db * K + 33) * N.of_nat (length entries) + 1)%N.
  Proof.
    intros p entries T_entry K Hplan HK Hclock Hentries initial.
    pose proof (fold_credit p entries T_entry K
      (D.unit (fold_left Facts.put_entry entries initial)) Hplan HK Hclock initial
      (Facts.init_invariant p) Hentries (Nat.le_refl _)) as Hfold.
    unfold initial in Hfold. rewrite D.potential_init in Hfold.
    fold initial in Hfold. nia.
  Qed.

End PointerSeedTime.

Module AndersenCode (V : VALUE_OPS with Definition t := positive)
    (I : INDEX_OPS V) (J : JOIN_OPS V I) (D : DATABASE_OPS V I)
    (R : RUN_OPS V I J D) <: ANDERSEN_OPS V I J D R.
  Definition compile (_ : pointer_input) : program V.t := andersen_program.
  Definition seed_put (db : D.t) (entry : positive * (positive * positive)) : D.t :=
    D.put (fst entry) [Val (fst (snd entry)); Val (snd (snd entry))] None db.
  Definition seed (q : pointer_input) : D.t :=
    fold_left seed_put (pointer_seed_entries 5 q)
      (D.init (decls V.t (compile q)) (pointer_plan_slots (R.plan (compile q)))).
  Definition solve (q : pointer_input) (lim : limits) : stop * D.t :=
    let p := compile q in R.run p (R.plan p) lim (seed q).
  Definition points (db : D.t) (x a : positive) : bool :=
    match fst (D.lookup 5 [Val x; Val a] db) with
    | Some None => true
    | _ => false
    end.
End AndersenCode.

Module Andersen (V : VALUE with Definition t := positive)
    (I : INDEX V) (J : JOIN V I) (D : DATABASE V I) (R : RUN V I J D) <: ANDERSEN V I J D R.
  Include AndersenCode V I J D R.
  Module Seeds := PointerSeedFacts V I J D R.

  (** The fixed inclusion program passes the source sort checker. *)
  Lemma program_sorted : forall q, program_ok (compile q).
  Proof.
    intro q; apply (proj1 (check_program_spec V.t (compile q))); vm_compute; reflexivity.
  Qed.

  (** Every seed entry targets a declared binary relation. *)
  Lemma seed_entries_ok : forall q, Forall (Seeds.entry_ok (compile q)) (pointer_seed_entries 5 q).
  Proof.
    intros [instructions initial]; cbn [pointer_seed_entries]; apply Forall_app; split.
    - apply Forall_forall; intros entry Hin; apply in_map_iff in Hin.
      destruct Hin as [instruction [Heq Hin]]; subst entry; destruct instruction; split; reflexivity.
    - apply Forall_forall; intros entry Hin; apply in_map_iff in Hin.
      destruct Hin as [[x y] [Heq Hin]]; subst entry; split; reflexivity.
  Qed.

  (** Seeding establishes well-formedness, the plan layout and identifier-free rows. *)
  Lemma seed_invariant : forall q, Seeds.invariant (compile q) (seed q).
  Proof.
    intro q; change (Seeds.invariant (compile q)
      (fold_left Seeds.put_entry (pointer_seed_entries 5 q)
        (D.init (decls V.t (compile q)) (Syntax.slots V.t (R.plan (compile q)))))).
    apply Seeds.fold_invariant.
    - apply R.plan_checked; apply program_sorted.
    - apply Seeds.init_invariant.
    - apply seed_entries_ok.
  Qed.

  Lemma compile_rules : forall q, compile q = andersen_program.
  Proof.
    reflexivity.
  Qed.

  Lemma rules_valid : forall q, valid V.prim V.merge (andersen_model q) (compile q).
  Proof.
    intro q; split.
    - exact (andersen_rule_valid V.prim q).
    - intros f m k a b Hkind Hlat Hlat'; exact Hlat.
  Qed.

  Lemma seed_rows : forall q f k o, row (D.view (seed q)) f k o <-> pointer_seed_row q f k o.
  Proof.
    intros q f k o.
    change (row (D.view (fold_left Seeds.put_entry (pointer_seed_entries 5 q)
      (D.init (decls V.t (compile q)) (Syntax.slots V.t (R.plan (compile q)))))) f k o <->
      pointer_seed_row q f k o).
    rewrite (Seeds.fold_rows (compile q) (pointer_seed_entries 5 q)
      (D.init (decls V.t (compile q)) (Syntax.slots V.t (R.plan (compile q))))
      (R.plan_checked (compile q) (program_sorted q)) (Seeds.init_invariant (compile q))
      (seed_entries_ok q) f k o).
    split.
    - intros [Hinitial | [[g [x y]] [Hin [Hf [Hk Ho]]]]].
      + apply (proj1 (proj1 (D.init_view (decls V.t (compile q))
          (Syntax.slots V.t (R.plan (compile q))) f k o 1 1))) in Hinitial; contradiction.
      + cbn [fst snd] in Hf, Hk; subst f k o.
        split; [reflexivity | exists x, y; split; [reflexivity |]].
        apply pointer_seed_entries_spec in Hin; exact Hin.
    - intros [Ho [x [y [Hk Hsource]]]]; subst k o; right.
      exists (f, (x, y)); split.
      + apply pointer_seed_entries_spec; exact Hsource.
      + repeat split; reflexivity.
  Qed.

  Lemma seed_loaded : forall q, R.loaded (compile q) (R.plan (compile q)) (seed q).
  Proof.
    intro q; exact (proj1 (proj2 (seed_invariant q))).
  Qed.

  Lemma seed_wf : forall q, D.wf (seed q) /\ D.canonical (seed q) /\ R.no_ids (seed q).
  Proof.
    intro q; destruct (seed_invariant q) as [Hwf [Hloaded Hnoids]].
    split; [exact Hwf | split; [apply Seeds.no_ids_canonical; exact Hnoids | exact Hnoids]].
  Qed.

  Lemma solve_run : forall q lim,
    solve q lim = R.run (compile q) (R.plan (compile q)) lim (seed q).
  Proof.
    reflexivity.
  Qed.

  Lemma points_spec : forall db x a, D.wf db -> D.canonical db ->
    reflect (row (D.view db) 5 [Val x; Val a] None) (points db x a).
  Proof.
    intros db x a Hwf Hcanonical.
    change (reflect (row (D.view db) 5 [Val x; Val a] None)
      (match fst (D.lookup 5 [Val x; Val a] db) with Some None => true | _ => false end)).
    rewrite (proj1 (D.lookup_spec 5 [Val x; Val a] db Hwf)).
    change (reflect (row (D.view db) 5 [Val x; Val a] None)
      (match D.old db 5 [Val x; Val a] with Some None => true | _ => false end)).
    destruct (D.old db 5 [Val x; Val a]) as [[c |] |] eqn:Hlookup.
    - constructor; intro Hrow.
      apply (proj2 (D.old_row db 5 [Val x; Val a] None Hwf)) in Hrow; congruence.
    - constructor; apply (proj1 (D.old_row db 5 [Val x; Val a] None Hwf)); exact Hlookup.
    - constructor; intro Hrow.
      apply (proj2 (D.old_row db 5 [Val x; Val a] None Hwf)) in Hrow; congruence.
  Qed.

  Lemma solve_wf : forall q lim, D.wf (snd (solve q lim)) /\ D.canonical (snd (solve q lim)).
  Proof.
    intros q lim; rewrite solve_run.
    destruct (R.run_wf (compile q) (R.plan (compile q)) lim (seed q)
      (R.plan_checked (compile q) (program_sorted q)) (proj1 (seed_wf q)) (seed_loaded q))
      as [Hwf [Hcanonical Hloaded]]; auto.
  Qed.

  Lemma solve_saturates : forall q lim,
    N.to_nat (max_iter lim) >= 2 * R.herbrand (compile q) (seed q) + 2 ->
    fst (solve q lim) = Saturated.
  Proof.
    intros q lim Hfuel; rewrite solve_run; apply R.run_terminates.
    - apply R.plan_checked; apply program_sorted.
    - exact (proj1 (seed_wf q)).
    - apply seed_loaded.
    - reflexivity.
    - reflexivity.
    - exact (proj2 (proj2 (seed_wf q))).
    - exact Hfuel.
  Qed.

  (** The exact seed rows satisfy the independent inclusion model. *)
  Lemma seed_sat : forall q, sat V.merge (andersen_model q) (fun _ => tt) (D.view (seed q)).
  Proof.
    intro q; split.
    - intros f key output Hrow; apply seed_rows in Hrow.
      destruct Hrow as [Ho [x [y [Hkey Hsource]]]]; subst output key.
      unfold holds; rewrite (proj1 (seed_loaded q) f).
      destruct Hsource as [[Hf Hin] | [[Hf Hin] | [[Hf Hin] | [[Hf Hin] | [Hf Hin]]]]];
        subst f; cbn [compile program_kind andersen_program decls lookup_kind map den
          andersen_model rel]; exists x, y; split; try reflexivity;
        unfold pointer_relation; intuition eauto using May_initial.
    - split; [intros i j Hsame; reflexivity |].
      intros f m key a b Hkind Hlat Hlat'; exact Hlat.
  Qed.

  (** Every returned database retains the declarations, layout and row sorts. *)
  Lemma solve_loaded : forall q lim,
    R.loaded (compile q) (R.plan (compile q)) (snd (solve q lim)).
  Proof.
    intros q lim; rewrite solve_run.
    exact (proj2 (proj2 (R.run_wf (compile q) (R.plan (compile q)) lim (seed q)
      (R.plan_checked (compile q) (program_sorted q)) (proj1 (seed_wf q)) (seed_loaded q)))).
  Qed.

  (** Sorted rows of the inclusion program have no output cells. *)
  Lemma solve_no_outputs : forall q lim f key output,
    row (D.view (snd (solve q lim))) f key output -> output = None.
  Proof.
    intros q lim f key output Hrow.
    destruct (solve_loaded q lim) as [Hkinds [Hslots Hsorted]].
    destruct (Hsorted f key output Hrow) as [out [Hsort [Hkind Houtput]]].
    rewrite Hkinds in Hkind; apply andersen_kind_relation in Hkind; subst out.
    destruct output as [[i | v] |]; [discriminate | discriminate | reflexivity].
  Qed.

  (** Every source seed row persists exactly through the inclusion run. *)
  Lemma solve_seed_rows : forall q lim f key output, pointer_seed_row q f key output ->
    row (D.view (snd (solve q lim))) f key output.
  Proof.
    intros q lim f key output Hseed.
    pose proof (proj2 (seed_rows q f key output) Hseed) as Hrow.
    destruct Hseed as [Ho [x [y [Hkey Hsource]]]]; subst key output.
    destruct (R.run_grows (compile q) (R.plan (compile q)) lim (seed q)
      (R.plan_checked (compile q) (program_sorted q)) (proj1 (seed_wf q)) (seed_loaded q))
      as [Hsame Hrows].
    rewrite <- solve_run in Hrows.
    destruct (Hrows f [Val x; Val y] None Hrow) as [output [Hnew Hle]].
    change (row (D.view (snd (solve q lim))) f [Val x; Val y] output) in Hnew.
    rewrite (solve_no_outputs q lim f [Val x; Val y] output Hnew) in Hnew; exact Hnew.
  Qed.

  Lemma solve_exact : forall q lim db, solve q lim = (Saturated, db) ->
    forall x a, points db x a = true <-> may_points q x a.
  Proof.
    intros q lim db Hsolve x a.
    pose proof (solve_wf q lim) as Hvalid; rewrite Hsolve in Hvalid; cbn [snd] in Hvalid.
    destruct Hvalid as [Hwf Hcanonical]; split.
    - intro Hpoints.
      assert (Hrow : row (D.view db) 5 [Val x; Val a] None).
      { destruct (points_spec db x a Hwf Hcanonical); [assumption | discriminate]. }
      destruct (R.run_sat (compile q) (R.plan (compile q)) lim (seed q)
        (andersen_model q) (fun _ => tt)
        (R.plan_checked (compile q) (program_sorted q)) (proj1 (seed_wf q)) (seed_loaded q)
        (valid_sorted_of_valid V.t V.prim V.merge (andersen_model q) (compile q) (rules_valid q))
        (seed_sat q)) as [nu [Hextends [Hrows Hrest]]].
      rewrite <- solve_run, Hsolve in Hrows; cbn [snd] in Hrows.
      specialize (Hrows 5%positive [Val x; Val a] None Hrow).
      pose proof (proj1 (solve_loaded q lim) 5%positive) as Hkind.
      rewrite Hsolve in Hkind; cbn [snd] in Hkind.
      unfold holds in Hrows; rewrite Hkind in Hrows.
      change (exists y b, ([inr x; inr a] : list (unit + positive)) = [inr y; inr b] /\
        pointer_relation q 5 y b) in Hrows.
      destruct Hrows as [y [b [Heq Hsource]]]; inversion Heq; subst y b.
      unfold pointer_relation in Hsource; intuition discriminate.
    - intro Hpoints; destruct (points_spec db x a Hwf Hcanonical) as [Hrow | Hnot];
        [reflexivity | exfalso; apply Hnot].
      apply (pointer_closed_source V.prim V.merge q (D.view db)).
      + apply (R.run_closed (compile q) (R.plan (compile q)) lim (seed q) db).
        * apply R.plan_checked; apply program_sorted.
        * exact (proj1 (seed_wf q)).
        * apply seed_loaded.
        * rewrite <- solve_run; exact Hsolve.
      + intros f key output Hseed; pose proof (solve_seed_rows q lim f key output Hseed) as Hrow.
        rewrite Hsolve in Hrow; exact Hrow.
      + intros key output Hrow; apply (solve_no_outputs q lim 5 key output).
        rewrite Hsolve; exact Hrow.
      + exact Hpoints.
  Qed.

End Andersen.

Module AndersenT (V : VALUE_T with Definition t := positive)
    (I : INDEX_T V) (J : JOIN_T V I) (D : DATABASE_T V I) (R : RUN_T V I J D) <: ANDERSEN_ALL V I J D R.
  Include Andersen V I J D R.
  TimeFun compile.
  TimeFun seed_put.
  TimeFun seed.
  TimeFun solve.
  TimeFun points.
  Definition k_rules : N := (R.c_run * 512 * 512 * 512 + 1)%N.
  Definition k_seed : N := (128 * (D.c_db + 1) * (k_rules + 32) * (k_rules + 32))%N.
  Definition k_wrap : N := 32%N.
  Definition c_andersen : N := (k_seed + D.c_db + k_wrap + 32)%N.
  Lemma T_seed_le : forall q,
    (T_seed q <= c_andersen *
      N.of_nat (length (constraints q) + length (initial_pointers q) + 1) *
      N.of_nat (D.unit (seed q)) * N.of_nat (N.to_nat (N.log2 (D.ids (seed q))) + 1))%N.
  Proof. Admitted. (* STUB *)

  Lemma T_compile_le : forall q, (T_compile q <= c_andersen)%N.
  Proof.
    intro q; time_unfold T_compile; time_simpl; unfold c_andersen, k_wrap; lia.
  Qed.

  Lemma T_points_le : forall db x a, D.wf db ->
    (T_points db x a <= c_andersen * (N.of_nat (3 * D.unit db) +
      N.of_nat (cell_bits V.encode (Val x) + cell_bits V.encode (Val a)) + 1))%N.
  Proof.
    intros db x a Hwf.
    pose proof (D.T_lookup_le 5 [Val x; Val a] db Hwf) as Hlookup.
    time_unfold T_points; time_simpl.
    cbn [length fold_right] in Hlookup.
    rewrite ?Nat2N.inj_add, ?Nat2N.inj_mul in *.
    unfold c_andersen, k_wrap; nia.
  Qed.

  Lemma T_solve_le : forall q lim, let p := compile q in let cp := R.plan p in
    (T_solve q lim <= T_compile q + T_seed q + R.T_plan p +
      R.T_run p cp lim (seed q) + c_andersen)%N.
  Proof.
    intros q lim; time_unfold T_solve; time_simpl; unfold c_andersen, k_wrap; lia.
  Qed.

  Lemma F1_source_closed : forall q, pointer_closed q (may_points q).
  Proof.
    exact pointer_source_closed.
  Qed.

  Lemma F2_source_least : forall q r, pointer_closed q r ->
    forall x a, may_points q x a -> r x a.
  Proof.
    exact pointer_source_least.
  Qed.

  Lemma F3_rule_valid : forall q r rho, In r (rules V.t (compile q)) ->
    Forall (model_atom V.prim (andersen_model q) (program_kind (compile q)) rho)
      (query V.t r) ->
    model_actions V.prim (andersen_model q) (program_kind (compile q)) rho (actions V.t r).
  Proof.
    exact (andersen_rule_valid V.prim).
  Qed.

  Lemma F4_seed_sat : forall q,
    sat V.merge (andersen_model q) (fun _ => tt) (D.view (seed q)).
  Proof.
    exact seed_sat.
  Qed.

  Lemma F5_derives_source : forall q x a,
    derives V.prim (compile q) (D.view (seed q)) 5 [Val x; Val a] -> may_points q x a.
  Proof.
    intros q x a Hderive.
    set (lim := Limits (N.of_nat (2 * R.herbrand (compile q) (seed q) + 2)) 0%N).
    assert (Hsaturated : fst (solve q lim) = Saturated).
    { apply solve_saturates; unfold lim; cbn [max_iter]; rewrite Nat2N.id; apply le_n. }
    destruct (solve q lim) as [st db] eqn:Hsolve; cbn [fst] in Hsaturated; subst st.
    apply (proj1 (solve_exact q lim db Hsolve x a)).
    pose proof (solve_wf q lim) as Hvalid; rewrite Hsolve in Hvalid; cbn [snd] in Hvalid.
    destruct Hvalid as [Hwf Hcanonical].
    destruct (points_spec db x a Hwf Hcanonical) as [Hrow | Hnot]; [reflexivity |].
    exfalso; apply Hnot.
    apply (pointer_derives_closed V.prim V.merge (compile q) (D.view (seed q)) (D.view db)).
    - apply (R.run_closed (compile q) (R.plan (compile q)) lim (seed q) db).
      + apply R.plan_checked; apply program_sorted.
      + exact (proj1 (seed_wf q)).
      + apply seed_loaded.
      + rewrite <- solve_run; exact Hsolve.
    - intros f key output Hrow; apply seed_rows in Hrow.
      pose proof (solve_seed_rows q lim f key output Hrow) as Hnew; rewrite Hsolve in Hnew; exact Hnew.
    - intros f key output Hrow; apply (solve_no_outputs q lim f key output).
      rewrite Hsolve; exact Hrow.
    - exact Hderive.
  Qed.

  Lemma F6_closed_source : forall q w, closed V.prim V.merge (compile q) w ->
    (forall f k o, row (D.view (seed q)) f k o -> row w f k o) ->
    forall x a, may_points q x a -> row w 5 [Val x; Val a] None.
  Proof. Admitted. (* PLAN-DEFECT: pointer_closed_source_counterexample has only Some (Val 1) outputs. *)

  Lemma F7_step_covered : forall q r instruction before after,
    pointer_closed q r -> In instruction (constraints q) -> memory_covered r before ->
    pointer_exec instruction before = Some after -> memory_covered r after.
  Proof.
    exact pointer_step_covered.
  Qed.

  Lemma T1_wrapper : forall q lim, let p := compile q in let cp := R.plan p in
    (T_solve q lim <= T_compile q + T_seed q + R.T_plan p +
      R.T_run p cp lim (seed q) + k_wrap)%N.
  Proof.
    intros q lim; time_unfold T_solve; time_simpl; unfold k_wrap; lia.
  Qed.

End AndersenT.

Module AndersenSound (V : VALUE with Definition t := positive)
    (I : INDEX V) (J : JOIN V I) (D : DATABASE V I) (R : RUN V I J D)
    (A : ANDERSEN V I J D R) (L : POINTER_LINK) <: ANDERSEN_SOUND V I J D R A L.
  (** The least source relation contains all seeds and is closed under its four instructions. *)
  Lemma F1_source_closed : forall q, pointer_closed q (may_points q).
  Proof.
    exact pointer_source_closed.
  Qed.

  (** Each concrete instruction preserves coverage by a source-closed relation. *)
  Lemma F7_step_covered : forall q r instruction before after,
    pointer_closed q r -> In instruction (constraints q) -> memory_covered r before ->
    pointer_exec instruction before = Some after -> memory_covered r after.
  Proof.
    exact pointer_step_covered.
  Qed.

  (** Every reachable concrete pointer appears in every saturated analysis result. *)
  Lemma concrete_sound : forall q lim db s, A.solve q lim = (Saturated, db) ->
    pointer_reachable (L.initial q) (L.step q) s -> forall x a,
      trie_get x (L.memory s) = Some a -> A.points db x a = true.
  Proof.
    intros q lim db s Hsolve Hreach.
    assert (Hcovered : memory_covered (may_points q) (L.memory s)).
    { induction Hreach as [s Hinitial | s t Hreach IH Hstep].
      - intros y b Hy; apply May_initial; eapply L.initial_coverage; eassumption.
      - destruct (L.step_update q s t Hstep) as [instruction [Hin Hexec]].
        eapply F7_step_covered; [apply F1_source_closed | exact Hin | exact IH | exact Hexec]. }
    intros x a Hget; apply (proj2 (A.solve_exact q lim db Hsolve x a)).
    apply Hcovered; exact Hget.
  Qed.
End AndersenSound.
