(** * Symbolic interprocedural tabulation

    Changed path edges drive internal propagation and matched return summaries.
    For example, a newly discovered callee exit wakes the callers of that callee entry fact.
    Builds on: FrameworkIde, BaseIndex, BaseSet and CostLoop. *)

From Stdlib Require Import List Bool NArith Lia.
From Galois.Cost Require Import CostMonad CostList CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseIndex BaseCertify.
From Galois.Lattice Require Import LatticeCore.
From Galois.Program Require Import ProgramCfg ProgramIcfg.
From Galois.Framework Require Import FrameworkUtil FrameworkMicro FrameworkIfds FrameworkIde.
Import List.ListNotations Cost.Notations.

Module Tab.

Definition vertex N D := (N * option D)%type.
Definition key := jkey.

(** A caller remembers its outer entry fact and the actual exploded call arc. *)
Definition incoming N E P D F := (vertex N D * Jump.arc N E P D F)%type.

(** An arc occurrence is identified by its edge and its input and output facts. *)
Definition arc_key {N E P D F} (a : Jump.arc N E P D F) :=
  (Jump.edge a, (snd (Jump.source a), snd (Jump.target a))).

Definition arc_enc {N E P D A F} (I : Ide.t N E P D A F) :=
  FrameworkKey.pair (Cfg.edge_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I))))
    (FrameworkKey.pair (FrameworkKey.option (Ifds.fact_enc (Ide.ifds I)))
      (FrameworkKey.option (Ifds.fact_enc (Ide.ifds I)))).

Definition incoming_enc {N E P D A F} (I : Ide.t N E P D A F) :=
  FrameworkKey.pair (IdeValue.key_enc I) (arc_enc I).

(** Arc occurrence keys are injective in their edge and optional-fact components. *)
Theorem arc_enc_laws {N E P D A F} (I : Ide.t N E P D A F) :
  encoding_laws (Cfg.edge_enc (Icfg.cfg (Ifds.icfg (Ide.ifds I)))) ->
  encoding_laws (Ifds.fact_enc (Ide.ifds I)) -> encoding_laws (arc_enc I).
Proof.
  intros HE HD; apply FrameworkKey.pair_laws; [exact HE|].
  apply FrameworkKey.pair_laws; apply FrameworkKey.option_laws; exact HD.
Qed.

(** Incoming occurrence keys retain both caller root and actual exploded call components. *)
Theorem incoming_enc_laws {N E P D A F} (I : Ide.t N E P D A F) :
  encoding_laws (IdeValue.key_enc I) -> encoding_laws (arc_enc I) ->
  encoding_laws (incoming_enc I).
Proof.
  apply FrameworkKey.pair_laws.
Qed.

(** All inventories are prepared once, outside the changed-key loop. *)
Record prepared (N E P D F : Type) := Prep {
  arcs : list (Jump.arc N E P D F);
  roots : list (vertex N D);
  outgoing : Index.t (vertex N D) (Jump.arc N E P D F);
  inventory : list (key N D)
}.
Arguments Prep {N E P D F}.
Arguments arcs {N E P D F}.
Arguments roots {N E P D F}.
Arguments outgoing {N E P D F}.
Arguments inventory {N E P D F}.

(** The pending set suppresses duplicate work without conflating caller and callee keys. *)
Record state (N E P D F : Type) := State {
  jumps : Map.t positive F;
  callers : Map.t (vertex N D) (Map.t positive (incoming N E P D F));
  ends : Map.t (vertex N D) (Map.t positive (Jump.arc N E P D F));
  work : list (key N D);
  pending : FinSet.t (key N D)
}.
Arguments State {N E P D F}.
Arguments jumps {N E P D F}.
Arguments callers {N E P D F}.
Arguments ends {N E P D F}.
Arguments work {N E P D F}.
Arguments pending {N E P D F}.

Definition prepare_c {N E P D A F} (I : Ide.t N E P D A F) start :=
  let* as_ := Jump.arcs_c I in
  let* rs := Jump.roots_c I start as_ in
  let* out := Index.group_by_c (IdeValue.key_enc I)
    (fun a => Cost.ret (Jump.source a)) as_ in
  let* vertices := fw_flat_map_c (fun a =>
    Cost.ret [Jump.source a; Jump.target a]) as_ in
  let* ks := fw_flat_map_c (fun r =>
    map_c (fun v => Cost.ret (r, v)) (r :: vertices)) rs in
  Cost.ret (Prep as_ rs out ks).

Definition prepare {N E P D A F} (I : Ide.t N E P D A F) start :=
  Cost.value (prepare_c I start).

Definition schedule_c {N E P D A F} (I : Ide.t N E P D A F)
    (k : key N D) (s : state N E P D F) :=
  let* queued := FinSet.mem_c (Jump.enc I) k (pending s) in
  if queued then Cost.ret s else
  let* ps := FinSet.add_c (Jump.enc I) k (pending s) in
  Cost.ret (State (jumps s) (callers s) (ends s) (k :: work s) ps).

Definition schedule {N E P D A F} (I : Ide.t N E P D A F) k s :=
  Cost.value (schedule_c I k s).

(** Scheduling changes only pending work and keeps every stored summary. *)
Theorem schedule_equation {N E P D A F} (I : Ide.t N E P D A F) k s :
  schedule I k s =
  if FinSet.mem (Jump.enc I) k (pending s) then s else
    State (jumps s) (callers s) (ends s) (k :: work s)
      (FinSet.add (Jump.enc I) k (pending s)).
Proof.
  unfold schedule, schedule_c; autorewrite with galois_cost.
  fold (FinSet.mem (Jump.enc I) k (pending s)).
  destruct (FinSet.mem (Jump.enc I) k (pending s));
    autorewrite with galois_cost; reflexivity.
Qed.

(** Scheduling retains both the membership traversal and any newly inserted pending key. *)
Theorem schedule_cost_equation {N E P D A F} (I : Ide.t N E P D A F) k s :
  Cost.ticks (schedule_c I k s) =
    (Cost.ticks (FinSet.mem_c (Jump.enc I) k (pending s)) +
      if FinSet.mem (Jump.enc I) k (pending s) then 0
      else Cost.ticks (FinSet.add_c (Jump.enc I) k (pending s)))%N.
Proof.
  unfold schedule_c; rewrite Cost.ticks_bind; fold (FinSet.mem (Jump.enc I) k (pending s)).
  destruct (FinSet.mem (Jump.enc I) k (pending s));
    autorewrite with galois_cost; lia.
Qed.

(** A redundant contribution performs no join and adds no work. *)
Definition update_c {N E P D A F} (I : Ide.t N E P D A F)
    (k : key N D) (candidate : F) (s : state N E P D F) :=
  let* old := Jump.lookup_c I (jumps s) k in
  Cost.step ;;
  let* covered := leb_c (Micro.lat (Ide.micro I)) candidate old in
  if covered then Cost.ret s else
  Cost.step ;;
  let* joined := join_c (Micro.lat (Ide.micro I)) old candidate in
  Cost.step ;;
  let* code := encode_c (Jump.enc I) k in
  let* js := Map.set_c positive_encoding code joined (jumps s) in
  schedule_c I k (State js (callers s) (ends s) (work s) (pending s)).

Definition update {N E P D A F} (I : Ide.t N E P D A F) k candidate s :=
  Cost.value (update_c I k candidate s).

(** Updating joins a new contribution only when the old value does not cover it. *)
Theorem update_equation {N E P D A F} (I : Ide.t N E P D A F) k f s :
  update I k f s =
  if leb (Micro.lat (Ide.micro I)) f (Jump.lookup I (jumps s) k) then s else
    schedule I k
      (State (Map.set positive_encoding (encode (Jump.enc I) k)
        (join (Micro.lat (Ide.micro I)) (Jump.lookup I (jumps s) k) f) (jumps s))
        (callers s) (ends s) (work s) (pending s)).
Proof.
  unfold update, update_c; autorewrite with galois_cost.
  fold (Jump.lookup I (jumps s) k).
  fold (leb (Micro.lat (Ide.micro I)) f (Jump.lookup I (jumps s) k)).
  destruct (leb (Micro.lat (Ide.micro I)) f (Jump.lookup I (jumps s) k));
    autorewrite with galois_cost; reflexivity.
Qed.

(** An update charges its lookup, order test, join, encoding, map insertion and scheduling. *)
Theorem update_cost_equation {N E P D A F} (I : Ide.t N E P D A F) k f s :
  Cost.ticks (update_c I k f s) =
    let old := Jump.lookup I (jumps s) k in
    (Cost.ticks (Jump.lookup_c I (jumps s) k) +
      (1 + Cost.ticks (leb_c (Micro.lat (Ide.micro I)) f old)) +
      if leb (Micro.lat (Ide.micro I)) f old then 0 else
        let joined := join (Micro.lat (Ide.micro I)) old f in
        let code := encode (Jump.enc I) k in
        2 + Cost.ticks (join_c (Micro.lat (Ide.micro I)) old f) +
        Cost.ticks (encode_c (Jump.enc I) k) +
        Cost.ticks (Map.set_c positive_encoding code joined (jumps s)) +
        Cost.ticks (schedule_c I k
          (State (Map.set positive_encoding code joined (jumps s))
            (callers s) (ends s) (work s) (pending s))))%N.
Proof.
  unfold update_c; autorewrite with galois_cost.
  fold (Jump.lookup I (jumps s) k).
  fold (leb (Micro.lat (Ide.micro I)) f (Jump.lookup I (jumps s) k)).
  destruct (leb (Micro.lat (Ide.micro I)) f (Jump.lookup I (jumps s) k));
    autorewrite with galois_cost.
  - lia.
  - fold (join (Micro.lat (Ide.micro I)) (Jump.lookup I (jumps s) k) f).
    fold (encode (Jump.enc I) k).
    fold (Map.set positive_encoding (encode (Jump.enc I) k)
      (join (Micro.lat (Ide.micro I)) (Jump.lookup I (jumps s) k) f) (jumps s)).
    lia.
Qed.

(** Return propagation composes call, callee summary and return in program order. *)
Definition return_c {N E P D A F} (I : Ide.t N E P D A F)
    (r : vertex N D) (call ret : Jump.arc N E P D F) (s : state N E P D F) :=
  let* matches := Jump.matches_c (Icfg.site_enc (Ifds.icfg (Ide.ifds I))) call ret in
  if matches then
    let* before := Jump.lookup_c I (jumps s) (r, Jump.source call) in
    let* inside := Jump.lookup_c I (jumps s) (Jump.target call, Jump.source ret) in
    Cost.step ;;
    let* pushed := Micro.compose_c (Ide.micro I) (Jump.weight call) before in
    Cost.step ;;
    let* body := Micro.compose_c (Ide.micro I) inside pushed in
    Cost.step ;;
    let* after := Micro.compose_c (Ide.micro I) (Jump.weight ret) body in
    update_c I (r, Jump.target ret) after s
  else Cost.ret s.

Definition return_ {N E P D A F} (I : Ide.t N E P D A F) r call ret s :=
  Cost.value (return_c I r call ret s).

(** A return joins the ground matched-return contribution using the current jump map. *)
Theorem return_equation {N E P D A F} (I : Ide.t N E P D A F) r a b s :
  return_ I r a b s =
  if Cost.value (Jump.matches_c (Icfg.site_enc (Ifds.icfg (Ide.ifds I))) a b) then
    update I (r, Jump.target b)
      (Micro.compose (Ide.micro I) (Jump.weight b)
        (Micro.compose (Ide.micro I)
          (Jump.lookup I (jumps s) (Jump.target a, Jump.source b))
          (Micro.compose (Ide.micro I) (Jump.weight a)
            (Jump.lookup I (jumps s) (r, Jump.source a))))) s
  else s.
Proof.
  unfold return_, return_c; autorewrite with galois_cost.
  destruct (Cost.value (Jump.matches_c (Icfg.site_enc (Ifds.icfg (Ide.ifds I))) a b));
    autorewrite with galois_cost; reflexivity.
Qed.

(** A call update reuses all known exits even when its incoming record already exists. *)
Definition call_c {N E P D A F} (I : Ide.t N E P D A F)
    (r : vertex N D) (a : Jump.arc N E P D F) (s : state N E P D F) :=
  let* bucket := Map.find_or_c (IdeValue.key_enc I) Map.empty (Jump.target a)
    (callers s) in
  Cost.step ;;
  let* code := encode_c (incoming_enc I) (r, arc_key a) in
  let* bucket := Map.set_c positive_encoding code (r, a) bucket in
  let* cs := Map.set_c (IdeValue.key_enc I) (Jump.target a) bucket (callers s) in
  let s := State (jumps s) cs (ends s) (work s) (pending s) in
  let* known := Map.find_or_c (IdeValue.key_enc I) Map.empty (Jump.target a) (ends s) in
  let* exits := Map.elements_c known in
  fold_left_c (fun s kv => return_c I r a (snd kv) s) exits s.

(** An exit update reuses all callers, including callers discovered before the exit. *)
Definition end_c {N E P D A F} (I : Ide.t N E P D A F)
    (r : vertex N D) (a : Jump.arc N E P D F) (s : state N E P D F) :=
  let* bucket := Map.find_or_c (IdeValue.key_enc I) Map.empty r (ends s) in
  Cost.step ;;
  let* code := encode_c (arc_enc I) (arc_key a) in
  let* bucket := Map.set_c positive_encoding code a bucket in
  let* es := Map.set_c (IdeValue.key_enc I) r bucket (ends s) in
  let s := State (jumps s) (callers s) es (work s) (pending s) in
  let* known := Map.find_or_c (IdeValue.key_enc I) Map.empty r (callers s) in
  let* incoming := Map.elements_c known in
  fold_left_c (fun s kv =>
    return_c I (fst (snd kv)) (snd (snd kv)) a s) incoming s.

(** Call registration retains the existing exits and immediately replays them for this caller. *)
Theorem call_equation {N E P D A F} (I : Ide.t N E P D A F) r a s :
  Cost.value (call_c I r a s) =
    let bucket := Map.find_or (IdeValue.key_enc I) Map.empty (Jump.target a) (callers s) in
    let code := encode (incoming_enc I) (r, arc_key a) in
    let cs := Map.set (IdeValue.key_enc I) (Jump.target a)
      (Map.set positive_encoding code (r, a) bucket) (callers s) in
    fold_left (fun s kv => return_ I r a (snd kv) s)
      (Map.elements (Map.find_or (IdeValue.key_enc I) Map.empty (Jump.target a) (ends s)))
      (State (jumps s) cs (ends s) (work s) (pending s)).
Proof.
  unfold call_c; autorewrite with galois_cost; reflexivity.
Qed.

(** Exit registration immediately replays this exit for every recorded caller. *)
Theorem end_equation {N E P D A F} (I : Ide.t N E P D A F) r a s :
  Cost.value (end_c I r a s) =
    let bucket := Map.find_or (IdeValue.key_enc I) Map.empty r (ends s) in
    let code := encode (arc_enc I) (arc_key a) in
    let es := Map.set (IdeValue.key_enc I) r
      (Map.set positive_encoding code a bucket) (ends s) in
    fold_left (fun s kv => return_ I (fst (snd kv)) (snd (snd kv)) a s)
      (Map.elements (Map.find_or (IdeValue.key_enc I) Map.empty r (callers s)))
      (State (jumps s) (callers s) es (work s) (pending s)).
Proof.
  unfold end_c; autorewrite with galois_cost; reflexivity.
Qed.

Definition arc_c {N E P D A F} (I : Ide.t N E P D A F)
    (r : vertex N D) (a : Jump.arc N E P D F) (s : state N E P D F) :=
  match Jump.kind a with
  | Icfg.Internal =>
    let* before := Jump.lookup_c I (jumps s) (r, Jump.source a) in
    Cost.step ;;
    let* after := Micro.compose_c (Ide.micro I) (Jump.weight a) before in
    update_c I (r, Jump.target a) after s
  | Icfg.Call _ => call_c I r a s
  | Icfg.Return _ => end_c I r a s
  end.

(** Arc propagation dispatches on the stored kind without rerunning client callbacks. *)
Theorem arc_equation {N E P D A F} (I : Ide.t N E P D A F) r a s :
  Cost.value (arc_c I r a s) =
    match Jump.kind a with
    | Icfg.Internal =>
      update I (r, Jump.target a)
        (Micro.compose (Ide.micro I) (Jump.weight a)
          (Jump.lookup I (jumps s) (r, Jump.source a))) s
    | Icfg.Call _ => Cost.value (call_c I r a s)
    | Icfg.Return _ => Cost.value (end_c I r a s)
    end.
Proof.
  unfold arc_c; destruct (Jump.kind a); autorewrite with galois_cost; reflexivity.
Qed.

(** An empty worklist is the only stopping condition of the jump engine. *)
Definition step_c {N E P D A F} (I : Ide.t N E P D A F)
    (p : prepared N E P D F) (s : state N E P D F) :
    Cost.t (state N E P D F + state N E P D F) :=
  match work s with
  | [] => Cost.ret (inr s)
  | (r, v) :: rest =>
    let* ps := FinSet.remove_c (Jump.enc I) (r, v) (pending s) in
    let s := State (jumps s) (callers s) (ends s) rest ps in
    let* out := Index.find_c (IdeValue.key_enc I) v (outgoing p) in
    let* s := fold_left_c (fun s a => arc_c I r a s) out s in
    Cost.ret (inl s)
  end.

Definition step {N E P D A F} (I : Ide.t N E P D A F) p s :=
  Cost.value (step_c I p s).

(** The plain loop step observes the charged callback value. *)
Theorem step_c_value {N E P D A F} (I : Ide.t N E P D A F) p s :
  Cost.value (step_c I p s) = step I p s.
Proof.
  reflexivity.
Qed.

(** Scheduling bottom keys once also supports algebras whose composition is non-strict. *)
Definition initial_c {N E P D A F} (I : Ide.t N E P D A F)
    (p : prepared N E P D F) :=
  let* s := fold_left_c (fun s k => schedule_c I k s) (inventory p)
    (State Map.empty Map.empty Map.empty [] FinSet.empty) in
  fold_left_c (fun s r => update_c I (r, r) (Micro.id (Ide.micro I)) s) (roots p) s.

Definition initial {N E P D A F} (I : Ide.t N E P D A F) p :=
  Cost.value (initial_c I p).

(** Initialization schedules the conservative inventory and joins every entry identity. *)
Theorem initial_equation {N E P D A F} (I : Ide.t N E P D A F) p :
  initial I p =
    fold_left (fun s r => update I (r, r) (Micro.id (Ide.micro I)) s) (roots p)
      (fold_left (fun s k => schedule I k s) (inventory p)
        (State Map.empty Map.empty Map.empty [] FinSet.empty)).
Proof.
  unfold initial, initial_c; autorewrite with galois_cost; reflexivity.
Qed.

(** Raw results distinguish fuel exhaustion from worklist completion. *)
Definition raw_c {N E P D A F} (I : Ide.t N E P D A F) start fuel :=
  let* p := prepare_c I start in
  let* s := initial_c I p in
  iterate (step_c I p) fuel s.

Definition raw {N E P D A F} (I : Ide.t N E P D A F) start fuel :=
  Cost.value (raw_c I start fuel).

(** Preparation builds a stable source index and a finite conservative key inventory. *)
Theorem prepare_equation {N E P D A F} (I : Ide.t N E P D A F) start :
  prepare I start =
    let as_ := Jump.arcs I in
    let rs := Cost.value (Jump.roots_c I start as_) in
    Prep as_ rs (Index.group_by (IdeValue.key_enc I) Jump.source as_)
      (flat_map (fun r =>
        map (fun v => (r, v))
          (r :: flat_map (fun a => [Jump.source a; Jump.target a]) as_)) rs).
Proof.
  unfold prepare, prepare_c; autorewrite with galois_cost.
  rewrite Index.group_by_c_value, !fw_flat_map_value.
  f_equal; apply flat_map_ext; intro r; autorewrite with galois_cost; reflexivity.
Qed.

(** The raw driver runs the prepared specialized step from its constructed initial state. *)
Theorem raw_equation {N E P D A F} (I : Ide.t N E P D A F) start fuel :
  raw I start fuel =
    Cost.value (iterate (step_c I (prepare I start)) fuel (initial I (prepare I start))).
Proof.
  unfold raw, raw_c; autorewrite with galois_cost; reflexivity.
Qed.

(** Certification retains an exhausted state and a rejected candidate as distinct outcomes. *)
Inductive outcome {N E P D A F} (I : Ide.t N E P D A F) start :=
  | Exhausted (s : state N E P D F)
  | Rejected (s : state N E P D F)
  | Certified (result : {m : Map.t positive F | jump_post I start (Jump.lookup I m)}).
Arguments Exhausted {N E P D A F I start}.
Arguments Rejected {N E P D A F I start}.
Arguments Certified {N E P D A F I start}.

(** The charged checker is evaluated once and certify attaches its reflection proof. *)
Definition certify_c {N E P D A F} (I : Ide.t N E P D A F) start
    (s : state N E P D F) : Cost.t (outcome I start) :=
  let checked := check_jumps_c I start (jumps s) in
  Cost.map (fun _ =>
    match certify (fun _ : unit => jump_post I start (Jump.lookup I (jumps s)))
      (fun _ => Cost.value checked)
      (fun _ H => check_jumps_sound I start (jumps s) H) tt with
    | Some certified =>
      Certified (exist _ (jumps s) (proj2_sig certified))
    | None => Rejected s
    end) checked.

Definition tabulate_c {N E P D A F} (I : Ide.t N E P D A F) start fuel :=
  let* result := raw_c I start fuel in
  match result with
  | inl s => Cost.ret (Exhausted s)
  | inr s => certify_c I start s
  end.

Definition tabulate {N E P D A F} (I : Ide.t N E P D A F) start fuel :=
  Cost.value (tabulate_c I start fuel).

(** The wrapper retains raw exhaustion and checks every stopped candidate. *)
Theorem outcome_equation {N E P D A F} (I : Ide.t N E P D A F) start fuel :
  tabulate I start fuel =
    match raw I start fuel with
    | inl s => Exhausted s
    | inr s => Cost.value (certify_c I start s)
    end.
Proof.
  unfold tabulate, tabulate_c; autorewrite with galois_cost.
  fold (raw I start fuel).
  destruct (raw I start fuel); reflexivity.
Qed.

(** A certificate denotes a post-solution over exactly the public ground rows. *)
Theorem certified_jump_post {N E P D A F} (I : Ide.t N E P D A F) start
    (certified : {m : Map.t positive F | jump_post I start (Jump.lookup I m)}) :
  jump_post I start (Jump.lookup I (proj1_sig certified)).
Proof.
  exact (proj2_sig certified).
Qed.

(** Certification charges the entire checker, including ground-row preparation. *)
Theorem certify_cost_equation {N E P D A F} (I : Ide.t N E P D A F) start s :
  Cost.ticks (certify_c I start s) = Cost.ticks (check_jumps_c I start (jumps s)).
Proof.
  unfold certify_c; apply Cost.ticks_map.
Qed.

(** Successful certification retains the reached candidate map unchanged. *)
Theorem certify_candidate {N E P D A F} (I : Ide.t N E P D A F) start s c :
  Cost.value (certify_c I start s) = Certified c -> proj1_sig c = jumps s.
Proof.
  unfold certify_c; rewrite Cost.value_map.
  destruct (certify
    (fun _ : unit => jump_post I start (Jump.lookup I (jumps s)))
    (fun _ => Cost.value (check_jumps_c I start (jumps s)))
    (fun _ H => check_jumps_sound I start (jumps s) H) tt) as [certificate|].
  - intro Heq; injection Heq as Heq; subst c; reflexivity.
  - discriminate.
Qed.

(** Checking a stopped jump candidate can reject or certify it but cannot invent exhaustion. *)
Theorem certify_not_exhausted {N E P D A F} (I : Ide.t N E P D A F) start s t :
  Cost.value (certify_c I start s) <> Exhausted t.
Proof.
  unfold certify_c; rewrite Cost.value_map.
  match goal with
  | |- context [match ?decision with Some _ => _ | None => _ end] => destruct decision
  end; discriminate.
Qed.

(** Every actual jump post-solution is accepted by the charged candidate checker. *)
Theorem certify_accepts {N E P D A F} (I : Ide.t N E P D A F) start s :
  jump_post I start (Jump.lookup I (jumps s)) ->
  exists c, Cost.value (certify_c I start s) = Certified c.
Proof.
  intro Hpost.
  assert (Hchecked : Cost.value (check_jumps_c I start (jumps s)) = true).
  { apply check_jumps_iff; exact Hpost. }
  unfold certify_c; rewrite Cost.value_map.
  match goal with
  | |- context [certify ?P ?check ?sound ?w] =>
    assert (Hex : exists certificate, certify P check sound w = Some certificate)
      by (apply (proj2 (certify_some_iff P check sound w)); exact Hchecked);
    destruct Hex as [certificate Hcertificate]; rewrite Hcertificate
  end.
  eexists; reflexivity.
Qed.

(** The wrapper cost includes preparation, work and the checker on a stopped map. *)
Theorem tabulate_cost_equation {N E P D A F} (I : Ide.t N E P D A F) start fuel :
  Cost.ticks (tabulate_c I start fuel) =
    (Cost.ticks (raw_c I start fuel) +
      match raw I start fuel with
      | inl _ => 0
      | inr s => Cost.ticks (check_jumps_c I start (jumps s))
      end)%N.
Proof.
  unfold tabulate_c; rewrite Cost.ticks_bind; fold (raw I start fuel).
  destruct (raw I start fuel); rewrite ?Cost.ticks_ret, ?certify_cost_equation;
    reflexivity.
Qed.

(** A tabulation step pops one key and propagates precisely its outgoing exploded arcs. *)
Theorem tabulate_equation {N E P D A F} (I : Ide.t N E P D A F) p s :
  step I p s =
  match work s with
  | [] => inr s
  | (r, v) :: rest =>
    inl (fold_left (fun s a => Cost.value (arc_c I r a s))
      (Index.find (IdeValue.key_enc I) v (outgoing p))
      (State (jumps s) (callers s) (ends s) rest
        (FinSet.remove (Jump.enc I) (r, v) (pending s))))
  end.
Proof.
  unfold step, step_c; destruct (work s) as [|[r v] rest]; [reflexivity|].
  autorewrite with galois_cost; reflexivity.
Qed.

End Tab.
