(** * Function summaries and bounded contexts

    Summary rows combine local effects and call-site lifting of callee summaries.
    For example, a recursive pair contributes one call row in each direction.
    Builds on: ProgramCalls, FrameworkRows and FrameworkStack. *)

From Stdlib Require Import List Bool Arith NArith.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCalls.
From Galois.Fixpoint Require Import FixpointSystem FixpointAnalysis.
From Galois.Framework Require Import FrameworkUtil FrameworkRows FrameworkStack.
Import List.ListNotations Cost.Notations.

Module Ctx.

(** Context inventories are finite support data for the generated row domain. *)
Record t (F P K : Type) := Make {
  ctx_enc : encoding K;
  contexts : list K;
  init_c : F -> Cost.t K;
  enter_c : P -> F -> K -> Cost.t (option K)
}.
Arguments Make {F P K}.
Arguments ctx_enc {F P K}.
Arguments contexts {F P K}.
Arguments init_c {F P K}.
Arguments enter_c {F P K}.

Definition init {F P K} (cx : t F P K) f := Cost.value (init_c cx f).
Definition enter {F P K} (cx : t F P K) p f k := Cost.value (enter_c cx p f k).

(** Insensitive contexts have one unit key and never reject a call. *)
Definition insensitive F P : t F P unit :=
  Make unit_encoding [tt] (fun _ => Cost.ret tt) (fun _ _ _ => Cost.ret (Some tt)).

Fixpoint take_c {P} k (xs : list P) : Cost.t (list P) :=
  Cost.step ;;
  match k, xs with
  | O, _ | _, [] => Cost.ret []
  | S k, x :: rest => Cost.map (cons x) (take_c k rest)
  end.

(** Charged truncation keeps the same innermost-first context as Stack.truncate. *)
Theorem take_value {P} k (xs : list P) :
  Cost.value (take_c k xs) = Stack.truncate k xs.
Proof.
  change (Cost.value (take_c k xs) = firstn k xs).
  revert xs; induction k as [|k IH]; intros [|x xs]; cbn [take_c firstn];
    autorewrite with galois_cost; rewrite ?IH; reflexivity.
Qed.

Fixpoint strings_c {P} k (sites : list P) : Cost.t (list (list P)) :=
  Cost.step ;;
  match k with
  | O => Cost.ret [[]]
  | S k =>
    let* shorter := strings_c k sites in
    let* longer := fw_flat_map_c
      (fun p => map_c (fun st => Cost.ret (p :: st)) shorter) sites in
    Cost.ret ([] :: longer)
  end.

(** Call strings enumerate finite site support and retain at most k innermost sites. *)
Definition call_string {F P} k (C : Calls.t F P) : t F P (list P) :=
  let sites := Cost.value (fw_flat_map_c (Calls.sites_of_c C) (Calls.functions C)) in
  Make (FrameworkKey.list (Calls.site_enc C)) (Cost.value (strings_c k sites))
    (fun _ => Cost.ret [])
    (fun p _ st => Cost.map Some (take_c k (p :: st))).

End Ctx.

Module Summary.

(** Summary callbacks compute without links or soundness evidence. *)
Record spec (F P A : Type) := Make {
  lat : lattice A;
  local_c : F -> Cost.t A;
  via_call_c : P -> F -> A -> Cost.t A
}.
Arguments Make {F P A}.
Arguments lat {F P A}.
Arguments local_c {F P A}.
Arguments via_call_c {F P A}.

Definition local {F P A} (sp : spec F P A) f := Cost.value (local_c sp f).
Definition via_call {F P A} (sp : spec F P A) p g a := Cost.value (via_call_c sp p g a).

(** Local rows precede resolved call rows in function/site/target occurrence order. *)
Inductive constraint (F P : Type) :=
  | SLocal (f : F)
  | SCall (p : P) (g : F).
Arguments SLocal {F P}.
Arguments SCall {F P}.

Definition row_enc {F P} (C : Calls.t F P) :=
  encoding_comap (fun r : constraint F P => Cost.ret
    (match r with SLocal f => inl f | SCall p g => inr (p, g) end))
    (FrameworkKey.sum (Calls.fn_enc C) (FrameworkKey.pair (Calls.site_enc C) (Calls.fn_enc C))).

(** Lawful function and site dictionaries give injective summary rows. *)
Theorem row_enc_laws {F P} (C : Calls.t F P) :
  encoding_laws (Calls.fn_enc C) -> encoding_laws (Calls.site_enc C) ->
  encoding_laws (row_enc C).
Proof.
  intros HF HP; apply encoding_comap_laws.
  - intros [f|p g] [f'|p' g'] Hcode; cbn in Hcode; congruence.
  - apply FrameworkKey.sum_laws; [exact HF|apply FrameworkKey.pair_laws; assumption].
Qed.

Definition rows_c {F P} (C : Calls.t F P) :=
  let* locals := map_c (fun f => Cost.ret (SLocal f)) (Calls.functions C) in
  let* calls := fw_flat_map_c (fun f =>
    Cost.step ;;
    let* sites := Calls.sites_of_c C f in
    fw_flat_map_c (fun p =>
      Cost.step ;;
      let* targets := Calls.resolve_c C p in
      map_c (fun g => Cost.ret (SCall p g)) targets) sites) (Calls.functions C) in
  app_c locals calls.

Definition get_c {F P A} (C : Calls.t F P) (sp : spec F P A) (r : constraint F P) :=
  match r with
  | SLocal f => Cost.ret (Rows.Make f [] (fun _ => Cost.step ;; local_c sp f))
  | SCall p g =>
    Cost.step ;;
    let* caller := Calls.caller_of_c C p in
    Cost.ret (Rows.Make caller [g] (fun fs =>
      match fs with
      | a :: _ => Cost.step ;; via_call_c sp p g a
      | [] => Cost.ret (bot (lat sp))
      end))
  end.

(** Preparation retains the caller lookup and compiled row plans once. *)
Definition prepare_c {F P A} (C : Calls.t F P) (sp : spec F P A) :=
  let* cs := rows_c C in
  let* plans := map_c (fun r => Cost.map (fun plan => (r, plan)) (get_c C sp r)) cs in
  let* table := Map.of_list_c (row_enc C) plans in
  Cost.ret (cs, table).

Definition prepared_get_c {F P A} (C : Calls.t F P) (sp : spec F P A) table r :=
  match r with
  | SLocal f => Map.find_or_c (row_enc C)
      (Rows.Make f [] (fun _ => Cost.ret (bot (lat sp)))) r table
  | SCall _ g => Map.find_or_c (row_enc C)
      (Rows.Make g [] (fun _ => Cost.ret (bot (lat sp)))) r table
  end.

(** Function summaries are ordinary joining analyses over the supplied lattice. *)
Definition analysis {F P A} (C : Calls.t F P) (sp : spec F P A) :=
  let '(cs, table) := Cost.value (prepare_c C sp) in
  Analysis.Make (Calls.fn_enc C) (row_enc C) (lat sp)
    (Rows.system cs (prepared_get_c C sp table)) (Rows.static cs (prepared_get_c C sp table))
    (Policy.by_code (Calls.fn_enc C)).

(** Summary analysis laws require no call semantics or resolver-coverage proof. *)
Theorem analysis_laws {F P A} (C : Calls.t F P) (sp : spec F P A) :
  encoding_laws (Calls.fn_enc C) -> encoding_laws (Calls.site_enc C) ->
  lattice_laws (lat sp) -> Analysis.laws (analysis C sp).
Proof.
  intros HF HP HL; unfold analysis.
  destruct (Cost.value (prepare_c C sp)) as [cs table]; constructor.
  - exact HF.
  - apply row_enc_laws; assumption.
  - exact HL.
  - apply Rows.static_laws.
Qed.

Definition ctx_get_c {F P K A} (C : Calls.t F P) (cx : Ctx.t F P K)
    (sp : spec F P A) (rk : constraint F P * K) :=
  let '(r, k) := rk in
  match r with
  | SLocal f => Cost.ret (Rows.Make (f, k) [] (fun _ => Cost.step ;; local_c sp f))
  | SCall p g =>
    Cost.step ;;
    let* caller := Calls.caller_of_c C p in
    Cost.step ;;
    let* entered := Ctx.enter_c cx p g k in
    match entered with
    | None => Cost.ret (Rows.Make (caller, k) [] (fun _ => Cost.ret (bot (lat sp))))
    | Some callee_ctx =>
      Cost.ret (Rows.Make (caller, k) [(g, callee_ctx)] (fun fs =>
        match fs with
        | a :: _ => Cost.step ;; via_call_c sp p g a
        | [] => Cost.ret (bot (lat sp))
        end))
    end
  end.

(** Context rows are context-major and use the client's admitted-call boundary. *)
Definition ctx_analysis {F P K A} (C : Calls.t F P) (cx : Ctx.t F P K)
    (sp : spec F P A) :=
  let base := Cost.value (rows_c C) in
  let rows := Cost.value (fw_flat_map_c (fun k =>
    map_c (fun r => Cost.ret (r, k)) base) (Ctx.contexts cx)) in
  let EX := FrameworkKey.pair (Calls.fn_enc C) (Ctx.ctx_enc cx) in
  let EC := FrameworkKey.pair (row_enc C) (Ctx.ctx_enc cx) in
  let table := Cost.value (map_c (fun rk =>
    Cost.map (fun plan => (rk, plan)) (ctx_get_c C cx sp rk)) rows) in
  let table := Cost.value (Map.of_list_c EC table) in
  let get := fun rk =>
    let '(r, k) := rk in
    let f := match r with SLocal f => f | SCall _ g => g end in
    Map.find_or_c EC (Rows.Make (f, k) [] (fun _ => Cost.ret (bot (lat sp)))) rk table in
  Analysis.Make EX EC (lat sp) (Rows.system rows get) (Rows.static rows get)
    (Policy.by_code EX).

(** Context analysis laws use explicit context-key laws and fixed-read coverage. *)
Theorem ctx_analysis_laws {F P K A} (C : Calls.t F P) (cx : Ctx.t F P K)
    (sp : spec F P A) :
  encoding_laws (Calls.fn_enc C) -> encoding_laws (Calls.site_enc C) ->
  encoding_laws (Ctx.ctx_enc cx) -> lattice_laws (lat sp) ->
  Analysis.laws (ctx_analysis C cx sp).
Proof.
  intros HF HP HK HL; unfold ctx_analysis; constructor.
  - apply FrameworkKey.pair_laws; assumption.
  - apply FrameworkKey.pair_laws; [apply row_enc_laws; assumption|exact HK].
  - exact HL.
  - apply Rows.static_laws.
Qed.

Definition reach_get_c {F} (EF : encoding F) f (m : Map.t F (FinSet.t F)) :=
  Map.find_or_c EF FinSet.empty f m.

(** Floyd closure is prepared once and contains reflexive reachability on listed functions. *)
Definition closure_c {F P} (C : Calls.t F P) :=
  let EF := Calls.fn_enc C in
  let* initial := map_c (fun f =>
    let* es := Calls.out_c C f in
    let* gs := map_c (fun e => Cost.ret (edge_callee e)) es in
    let* set := FinSet.of_list_c EF (f :: gs) in
    Cost.ret (f, set)) (Calls.functions C) in
  let* initial := Map.of_list_c EF initial in
  fold_left_c (fun m pivot =>
    let* through := reach_get_c EF pivot m in
    let* rows := map_c (fun f =>
      let* old := reach_get_c EF f m in
      let* yes := FinSet.mem_c EF pivot old in
      let* result := if yes then FinSet.union_c old through else Cost.ret old in
      Cost.ret (f, result)) (Calls.functions C) in
    Map.of_list_c EF rows) (Calls.functions C) initial.

(** The SCC policy orders by reachable-set size and widens at the first code in each SCC. *)
Definition policy_scc {F P} (C : Calls.t F P) : Policy.t F :=
  let EF := Calls.fn_enc C in
  let closure := Cost.value (closure_c C) in
  let rows := Cost.value (map_c (fun f =>
    let* reach := reach_get_c EF f closure in
    let* count := FinSet.size_c reach in
    let* members := filter_c (fun g =>
      let* rg := reach_get_c EF g closure in
      let* fg := FinSet.mem_c EF g reach in
      let* gf := FinSet.mem_c EF f rg in
      Cost.ret (fg && gf)) (Calls.functions C) in
    let* component := FinSet.of_list_c EF members in
    let* members := FinSet.elements_c component in
    let* head := match members with
      | [] => Cost.ret false
      | g :: _ => eqb_c EF f g
      end in
    Cost.ret (f, (Pos.of_succ_nat count, head))) (Calls.functions C)) in
  let table := Cost.value (Map.of_list_c EF rows) in
  Policy.Make
    (fun f =>
      let* found := Map.get_c EF f table in
      match found with
      | Some pr => Cost.ret (fst pr)
      | None => Cost.step ;; encode_c EF f
      end)
    (fun f => Cost.map (fun found =>
      match found with Some pr => snd pr | None => false end) (Map.get_c EF f table))
    0 0.

Arguments analysis {F P A} C sp : simpl never.
Arguments ctx_analysis {F P K A} C cx sp : simpl never.
Arguments policy_scc {F P} C : simpl never.

End Summary.

Definition summary_analysis := @Summary.analysis.
Definition ctx_summary_analysis := @Summary.ctx_analysis.
Definition summary_policy_scc := @Summary.policy_scc.
Arguments summary_analysis {F P A}.
Arguments ctx_summary_analysis {F P K A}.
Arguments summary_policy_scc {F P}.
