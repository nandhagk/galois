(** * Prepared sparse SSA constraints

    Sparse rows share a lifted value carrier for values, edges and blocks.
    For example, an infeasible client guard keeps its edge unreachable.
    Builds on: ProgramSsa, DomainsValue, FrameworkRows and LatticeAdjoin. *)

From Stdlib Require Import List Bool Arith.
From Galois.Cost Require Import CostMonad CostList.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet.
From Galois.Lattice Require Import LatticeCore LatticeAdjoin.
From Galois.Graph Require Import GraphModel.
From Galois.Program Require Import ProgramCfg ProgramSsa.
From Galois.Domains Require Import DomainsValue.
From Galois.Fixpoint Require Import FixpointSystem FixpointAnalysis.
From Galois.Framework Require Import FrameworkUtil FrameworkRows.
Import List.ListNotations Cost.Notations.

Module Sparse.

(** Unknown tags distinguish values, edge occurrences and blocks. *)
Inductive unknown (N E V : Type) :=
  | UVal (v : V)
  | UEdge (e : E)
  | UBlock (b : N).
Arguments UVal {N E V}.
Arguments UEdge {N E V}.
Arguments UBlock {N E V}.

(** Rows retain all seven legacy constructors and their argument order. *)
Inductive constraint (N E V : Type) :=
  | CBlockEntry (b : N)
  | CEntryFact (v : V)
  | COp (v : V)
  | CArbitrary (v : V)
  | CArg (e : E) (i : nat)
  | CEdge (e : E)
  | CBlock (e : E).
Arguments CBlockEntry {N E V}.
Arguments CEntryFact {N E V}.
Arguments COp {N E V}.
Arguments CArbitrary {N E V}.
Arguments CArg {N E V}.
Arguments CEdge {N E V}.
Arguments CBlock {N E V}.

Definition unknown_enc {N E V} (EN : encoding N) (EE : encoding E) (EV : encoding V) :=
  encoding_comap (fun x : unknown N E V => Cost.ret
    (match x with UVal v => inl v | UEdge e => inr (inl e) | UBlock n => inr (inr n) end))
    (FrameworkKey.sum EV (FrameworkKey.sum EE EN)).

(** Sparse unknown keys preserve each constructor and component key. *)
Theorem unknown_enc_laws {N E V} (EN : encoding N) (EE : encoding E) (EV : encoding V) :
  encoding_laws EN -> encoding_laws EE -> encoding_laws EV ->
  encoding_laws (unknown_enc EN EE EV).
Proof.
  intros HN HE HV; apply encoding_comap_laws.
  - intros [v|e|n] [w|f|m] Hcode; cbn in Hcode; congruence.
  - apply FrameworkKey.sum_laws; [exact HV|apply FrameworkKey.sum_laws; assumption].
Qed.

Definition row_key {N E V} (c : constraint N E V) :
    nat * (option N * (option E * (option V * nat))) :=
  match c with
  | CBlockEntry n => (0, (Some n, (None, (None, 0))))
  | CEntryFact v => (1, (None, (None, (Some v, 0))))
  | COp v => (2, (None, (None, (Some v, 0))))
  | CArbitrary v => (3, (None, (None, (Some v, 0))))
  | CArg e i => (4, (None, (Some e, (None, i))))
  | CEdge e => (5, (None, (Some e, (None, 0))))
  | CBlock e => (6, (None, (Some e, (None, 0))))
  end.

Definition constraint_enc {N E V} (EN : encoding N) (EE : encoding E) (EV : encoding V) :=
  encoding_comap (fun c => Cost.ret (row_key c))
    (FrameworkKey.pair nat_encoding (FrameworkKey.pair (FrameworkKey.option EN)
      (FrameworkKey.pair (FrameworkKey.option EE)
        (FrameworkKey.pair (FrameworkKey.option EV) nat_encoding)))).

(** Sparse row tags and indexed argument slots have injective keys. *)
Theorem constraint_enc_laws {N E V} (EN : encoding N) (EE : encoding E) (EV : encoding V) :
  encoding_laws EN -> encoding_laws EE -> encoding_laws EV ->
  encoding_laws (constraint_enc EN EE EV).
Proof.
  intros HN HE HV; apply encoding_comap_laws.
  - intros [n|v|v|v|e i|e|e] [m|w|w|w|f j|f|f] Hcode;
      rewrite !Cost.value_ret in Hcode; cbn [row_key] in Hcode; congruence.
  - repeat apply FrameworkKey.pair_laws;
      try apply FrameworkKey.option_laws; assumption || apply nat_encoding_laws.
Qed.

(** Entry arguments are charged readers, separate from the value-domain laws. *)
Record t (N E V K G A : Type) := Make {
  ssa : Ssa.t N E V K G;
  dom : ValueAbs.t A K G;
  entry_arg_c : V -> Cost.t A
}.
Arguments Make {N E V K G A}.
Arguments ssa {N E V K G A}.
Arguments dom {N E V K G A}.
Arguments entry_arg_c {N E V K G A}.

Definition entry_arg {N E V K G A} (P : t N E V K G A) v :=
  Cost.value (entry_arg_c P v).

(** A prepared guard retains each subject's immediate operation definition. *)
Definition guard_plan N V K G := (G * list V * list (V * definition N V K))%type.

Definition guard_plan_c {N E V K G} (S : Ssa.t N E V K G) (gd : G * list V) :=
  let* defs := map_c (fun v =>
    Cost.step ;; Cost.map (fun d => (v, d)) (Ssa.def_c S v)) (snd gd) in
  Cost.ret (fst gd, snd gd, defs).

Definition guard_deps_c {N V K G} (gd : guard_plan N V K G) :=
  let '(_, ys, defs) := gd in
  let* args := fw_flat_map_c (fun vd =>
    Cost.ret (match snd vd with Op _ args => args | _ => [] end)) defs in
  app_c ys args.

(** Missing operands propagate fresh unreachable bottom. *)
Fixpoint collect_c {A} (fs : list (option A)) : Cost.t (option (list A)) :=
  Cost.step ;;
  match fs with
  | [] => Cost.ret (Some [])
  | None :: _ => Cost.ret None
  | Some a :: rest => Cost.map (option_map (cons a)) (collect_c rest)
  end.

Fixpoint zip_c {X A} (xs : list X) (fs : list A) : Cost.t (list (X * A)) :=
  Cost.step ;;
  match xs, fs with
  | x :: xs, f :: fs => Cost.map (cons (x, f)) (zip_c xs fs)
  | _, _ => Cost.ret []
  end.

Definition read_values_c {V A} (EV : encoding V) (m : Map.t V (option A)) xs :=
  map_c (fun v => Map.find_or_c EV None v m) xs.

(** Right-fold updates retain the first occurrence when an operand is repeated. *)
Definition put_values_c {V A} (EV : encoding V) xs (fs : list A)
    (m : Map.t V (option A)) :=
  let* pairs := zip_c xs fs in
  fold_right_c (fun va m => Map.set_c EV (fst va) (Some (snd va)) m) m pairs.

Definition back_one_c {N V K G A} (EV : encoding V) (D : ValueAbs.t A K G)
    (m : Map.t V (option A)) (vd : V * definition N V K) :=
  match snd vd with
  | Op k args =>
    let* result := Map.find_or_c EV None (fst vd) m in
    let* fs := read_values_c EV m args in
    let* values := collect_c fs in
    match result, values with
    | Some a, Some values =>
      Cost.step ;;
      let* refined := ValueAbs.back_c D k a values in
      put_values_c EV args refined m
    | _, _ => Cost.ret m
    end
  | _ => Cost.ret m
  end.

(** Guards use stored subject facts and then propagate one operation level backward. *)
Definition guard_one_c {N V K G A} (EV : encoding V) (D : ValueAbs.t A K G)
    (m : Map.t V (option A)) (gd : guard_plan N V K G) :=
  let '(g, ys, defs) := gd in
  let* fs := read_values_c EV m ys in
  let* values := collect_c fs in
  match values with
  | None => Cost.ret None
  | Some values =>
    Cost.step ;;
    let* refined := ValueAbs.guard_c D g values in
    let* m := put_values_c EV ys refined m in
    let* m := fold_left_c (back_one_c EV D) defs m in
    Cost.ret (Some m)
  end.

(** Guard order threads refinements through the changing fact map. *)
Definition guards_c {N V K G A} (EV : encoding V) (D : ValueAbs.t A K G)
    (gds : list (guard_plan N V K G)) (m : Map.t V (option A)) :=
  fold_left_c (fun acc gd =>
    match acc with
    | None => Cost.ret None
    | Some m => guard_one_c EV D m gd
    end) gds (Some m).

Definition snapshot_c {V A} (EV : encoding V) xs (fs : list (option A)) :=
  let* pairs := zip_c xs fs in
  Map.of_list_c EV pairs.

Definition feasible_c {V A K G} (EV : encoding V) (D : ValueAbs.t A K G) xs m :=
  forallb_c (fun v =>
    let* a := Map.find_or_c EV None v m in
    match a with
    | None => Cost.ret false
    | Some a => Cost.step ;; Cost.map negb (leb_c (ValueAbs.lat D) a (bot (ValueAbs.lat D)))
    end) xs.

Definition value_row_c {N E V K G A} (P : t N E V K G A) entries v :
    Cost.t (list (constraint N E V * Rows.t (unknown N E V) (option A))) :=
  let S := ssa P in
  let D := dom P in
  Cost.step ;;
  let* d := Ssa.def_c S v in
  match d with
  | Op k args =>
    let* keys := map_c (fun v => Cost.ret (UVal v)) args in
    Cost.ret [(COp v, Rows.Make (UVal v) keys (fun fs =>
      let* values := collect_c fs in
      match values with
      | None => Cost.ret None
      | Some vs => Cost.step ;; Cost.map Some (ValueAbs.op_c D k vs)
      end))]
  | Param b _ =>
    let* is_entry := FinSet.mem_c (Cfg.node_enc (Ssa.cfg S)) b entries in
    if is_entry then
      Cost.ret [(CEntryFact v, Rows.Make (UVal v) [] (fun _ =>
        Cost.step ;; Cost.map Some (entry_arg_c P v)))]
    else Cost.ret []
  | Arbitrary =>
    Cost.ret [(CArbitrary v, Rows.Make (UVal v) []
      (fun _ => Cost.ret (Some (ValueAbs.top D))))]
  end.

Definition refine_c {N E V K G A} (P : t N E V K G A)
    (gds : list (guard_plan N V K G)) xs fs :=
  let* m := snapshot_c (Ssa.val_enc (ssa P)) xs fs in
  guards_c (Ssa.val_enc (ssa P)) (dom P) gds m.

Definition edge_rows_c {N E V K G A} (P : t N E V K G A) e :
    Cost.t (list (constraint N E V * Rows.t (unknown N E V) (option A))) :=
  let S := ssa P in
  let D := dom P in
  let g := Cfg.graph (Ssa.cfg S) in
  Cost.step ;;
  let* src := Graph.source_c g e in
  Cost.step ;;
  let* dst := Graph.target_c g e in
  Cost.step ;;
  let* actuals := Ssa.args_c S e in
  Cost.step ;;
  let* params := Ssa.params_c S dst in
  Cost.step ;;
  let* gd := Ssa.guards_c S e in
  let* gds := map_c (guard_plan_c S) gd in
  let* vars := fw_flat_map_c guard_deps_c gds in
  let* keys := map_c (fun v => Cost.ret (UVal v)) vars in
  let edge := (CEdge e, Rows.Make (UEdge e) (UBlock src :: keys) (fun fs =>
    match fs with
    | Some _ :: rest =>
      let* refined := refine_c P gds vars rest in
      match refined with
      | None => Cost.ret None
      | Some m =>
        let* feasible := feasible_c (Ssa.val_enc S) D vars m in
        Cost.ret (if feasible then Some (ValueAbs.top D) else None)
      end
    | _ => Cost.ret None
    end)) in
  let block := (CBlock e, Rows.Make (UBlock dst) [UEdge e] (fun fs =>
    Cost.ret (match fs with a :: _ => a | _ => None end))) in
  let* count := length_c actuals in
  let* slots := fw_seq_c 0 count in
  let* argrows := map_c (fun i =>
    let* param := fw_nth_c params i in
    let* actual := fw_nth_c actuals i in
    match param, actual with
    | Some y, Some z =>
      let* zs := app_c [z] vars in
      let* reads := map_c (fun v => Cost.ret (UVal v)) zs in
      Cost.ret (CArg e i, Rows.Make (UVal y) (UEdge e :: reads) (fun fs =>
        match fs with
        | Some _ :: rest =>
          let* refined := refine_c P gds zs rest in
          match refined with
          | None => Cost.ret None
          | Some m => Map.find_or_c (Ssa.val_enc S) None z m
          end
        | _ => Cost.ret None
        end))
    | _, _ => Cost.ret (CArg e i, Rows.Make (UEdge e) [] (fun _ => Cost.ret None))
    end) slots in
  Cost.ret (edge :: block :: argrows).

(** Preparation retains entry rows, then value order, then edge/ block/ argument order. *)
Definition prepare_c {N E V K G A} (P : t N E V K G A) :=
  let cfg := Ssa.cfg (ssa P) in
  let* entries := FinSet.of_list_c (Cfg.node_enc cfg) (Graph.entries (Cfg.graph cfg)) in
  let* seeds := map_c (fun b =>
    Cost.ret (CBlockEntry b, Rows.Make (UBlock b) []
      (fun _ => Cost.ret (Some (ValueAbs.top (dom P)))))) (Graph.entries (Cfg.graph cfg)) in
  let* values := fw_flat_map_c (value_row_c P entries) (Ssa.values (ssa P)) in
  let* es := fw_edges_c cfg in
  let* edges := fw_flat_map_c (edge_rows_c P) es in
  let* tail := app_c values edges in
  app_c seeds tail.

Definition rows {N E V K G A} (P : t N E V K G A) :=
  map fst (Cost.value (prepare_c P)).

Definition row_enc {N E V K G A} (P : t N E V K G A) :=
  constraint_enc (Cfg.node_enc (Ssa.cfg (ssa P))) (Cfg.edge_enc (Ssa.cfg (ssa P)))
    (Ssa.val_enc (ssa P)).

Definition key_enc {N E V K G A} (P : t N E V K G A) :=
  unknown_enc (Cfg.node_enc (Ssa.cfg (ssa P))) (Cfg.edge_enc (Ssa.cfg (ssa P)))
    (Ssa.val_enc (ssa P)).

(** The entry argument supplies a total fallback target for malformed unlisted rows. *)
Definition get_c {N E V K G A} (P : t N E V K G A) (entry : N)
    (table : Map.t (constraint N E V) (Rows.t (unknown N E V) (option A))) c :=
  Map.find_or_c (row_enc P) (Rows.Make (UBlock entry) [] (fun _ => Cost.ret None)) c table.

Definition analysis_c {N E V K G A} (P : t N E V K G A) entry :=
  let* prepared := prepare_c P in
  let* table := Map.of_list_c (row_enc P) prepared in
  let* cs := map_c (fun cr => Cost.ret (fst cr)) prepared in
  Cost.ret (Analysis.Make (key_enc P) (row_enc P) (lift_bot (ValueAbs.lat (dom P)))
    (Rows.system cs (get_c P entry table)) (Rows.static cs (get_c P entry table))
    (Policy.by_code (key_enc P))).

Definition analysis {N E V K G A} (P : t N E V K G A) entry :=
  Cost.value (analysis_c P entry).

(** Sparse static summaries are obtained from the same retained row plans. *)
Definition static {N E V K G A} (P : t N E V K G A) entry :=
  Analysis.static (analysis P entry).

(** Prepared sparse summaries cover all reads without any value-law premise. *)
Theorem static_laws {N E V K G A} (P : t N E V K G A) entry :
  System.static_laws (static P entry).
Proof.
  unfold static, analysis, analysis_c; autorewrite with galois_cost.
  apply Rows.static_laws.
Qed.

(** Generated analysis laws need encodings and weak value order laws, without semantics. *)
Theorem analysis_laws {N E V K G A} (P : t N E V K G A) entry :
  encoding_laws (Cfg.node_enc (Ssa.cfg (ssa P))) ->
  encoding_laws (Cfg.edge_enc (Ssa.cfg (ssa P))) ->
  encoding_laws (Ssa.val_enc (ssa P)) ->
  lattice_laws (ValueAbs.lat (dom P)) -> Analysis.laws (analysis P entry).
Proof.
  intros HN HE HV HL; unfold analysis, analysis_c; autorewrite with galois_cost.
  constructor.
  - apply unknown_enc_laws; assumption.
  - apply constraint_enc_laws; assumption.
  - apply lift_bot_laws; exact HL.
  - apply Rows.static_laws.
Qed.

Arguments prepare_c {N E V K G A} P : simpl never.
Arguments analysis_c {N E V K G A} P entry : simpl never.
Arguments analysis {N E V K G A} P entry : simpl never.

End Sparse.

(** Sparse analysis runs from computational SSA and value dictionaries alone. *)
Definition sparse_analysis := @Sparse.analysis.
Arguments sparse_analysis {N E V K G A}.
