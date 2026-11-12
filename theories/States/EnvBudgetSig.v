(** * Word environment budgets

    Word budgets connect canonical payloads, typed instructions and system rows.
    For example, an assignment keeps the declared width of its destination variable.
    Builds on: WordSig, BitsLang, EnvSig and SystemSig. *)

From Stdlib Require Import List ZArith Bool.
From Argent Require Import Time Std.
From Galois.Base Require Import KeySig MapSig.
From Galois.Bits Require Import Word Op.
From Galois.Domains Require Import LangSig ValueSig WordSig BitsLang CongruenceSig Congruence.
From Galois.States Require Import EnvSig.
From Galois.Fixpoint Require Import SystemSig WorklistSig.

Local Open Scope nat_scope.

(** This leaf wiring fixes the concrete primitives used by congruence envelopes. *)
Module WordBudgetOps <: WORD_LANGUAGE_OPS.
  Definition op := Op.op.
  Definition wrap := Word.wrap.
  Definition signed := Word.signed.
  Definition eval_op := Op.eval_op.
  Definition result_width := Op.result_width.
End WordBudgetOps.

Module CongruenceBudgetCode := CongruenceCode WordBudgetOps.

Module Type CONGRUENCE_BUDGET_CODE_LINK (L : WORD_LANGUAGE_T) (W : CONGRUENCE_ALL L).
  (** Normalization is the concrete congruence algorithm. *)
  Parameter norm_code : W.congr_norm = CongruenceBudgetCode.congr_norm.
  (** Joining uses the concrete normalized gcd algorithm. *)
  Parameter join_code : W.pjoin = CongruenceBudgetCode.pjoin.
  (** Meeting uses the concrete normalized Chinese remainder algorithm. *)
  Parameter meet_code : W.pmeet = CongruenceBudgetCode.pmeet.
  (** Bottom uses the concrete congruence constructor. *)
  Parameter bot_code : W.pbot = CongruenceBudgetCode.pbot.
  (** Top uses the concrete universal congruence. *)
  Parameter top_code : W.ptop = CongruenceBudgetCode.ptop.
  (** Constants use the concrete wrapped singleton algorithm. *)
  Parameter const_code : W.pconst = CongruenceBudgetCode.pconst.
  (** Widening keeps stable payloads and otherwise joins them. *)
  Parameter widen_code : forall q w a b, W.pwiden q w a b =
    if W.pleb w b a then a else W.pjoin w a b.
  (** Narrowing uses the concrete congruence meet. *)
  Parameter narrow_code : W.pnarrow = W.pmeet.
End CONGRUENCE_BUDGET_CODE_LINK.

(** Typed terms check each operator's actual result-width function. *)
Inductive word_term_typed {X : Type} (variables : list X) (width_of : X -> positive)
    : term bop X -> positive -> Prop :=
  | WTLeaf : forall x, In x variables -> word_term_typed variables width_of (Leaf x) (width_of x)
  | WTConst : forall w z, word_term_typed variables width_of (Node (BConst w z) nil) w
  | WTOp : forall o es ws w,
      word_terms_typed variables width_of es ws ->
      Op.result_width o ws = Some w ->
      word_term_typed variables width_of (Node (BOp o) es) w
with word_terms_typed {X : Type} (variables : list X) (width_of : X -> positive)
    : list (term bop X) -> list positive -> Prop :=
  | WTNil : word_terms_typed variables width_of nil nil
  | WTCons : forall e es w ws,
      word_term_typed variables width_of e w ->
      word_terms_typed variables width_of es ws ->
      word_terms_typed variables width_of (e :: es) (w :: ws).

Inductive word_instruction (X G : Type) :=
  | WAssign (x : X) (e : term bop X)
  | WHavoc (x : X)
  | WAssume (g : G) (es : list (term bop X))
  | WIdentity.

Arguments WAssign {X G} x e.
Arguments WHavoc {X G} x.
Arguments WAssume {X G} g es.
Arguments WIdentity {X G}.

(** Untagging accepts only explicitly width-indexed payloads. *)
Fixpoint budget_untag {P} (xs : list (tagged P)) : option (list (positive * P)) :=
  match xs with
  | nil => Some nil
  | TVal w p :: xs =>
    match budget_untag xs with Some ys => Some ((w, p) :: ys) | None => None end
  | _ => None
  end.
TimeFun budget_untag.

(** Payload normalization collapses recognized bottoms into the common tag. *)
Definition budget_norm {P} (is_bot : positive -> P -> bool) w p : tagged P :=
  if is_bot w p then TBot else TVal w p.
TimeFun budget_norm.

(** Tagged binary operations combine payloads only at equal widths. *)
Definition budget_binary {P} (is_bot : positive -> P -> bool)
    (operation : positive -> P -> P -> P) (a b : tagged P) : tagged P :=
  match a, b with
  | TBot, x | x, TBot => x
  | TVal w p, TVal w' q =>
    if Pos.eqb w w' then budget_norm is_bot w (operation w p q) else TAny
  | _, _ => TAny
  end.
TimeFun budget_binary.

(** Tagged intersections retain a known width when the other operand is top. *)
Definition budget_intersection {P} (is_bot : positive -> P -> bool)
    (operation : positive -> P -> P -> P) (a b : tagged P) : tagged P :=
  match a, b with
  | TBot, _ | _, TBot => TBot
  | TAny, x | x, TAny => x
  | TVal w p, TVal w' q =>
    if Pos.eqb w w' then budget_norm is_bot w (operation w p q) else TBot
  end.
TimeFun budget_intersection.

Module Type WORD_PAYLOAD_ENVELOPE (L : WORD_LANGUAGE_T) (W : WORD_PAYLOAD_T L).
  (* spec: canonical payload_size_bound payload_rank_bound *)
  Parameter canonical : positive -> W.p -> Prop.
  Parameter payload_size_bound : positive -> nat.
  Parameter payload_rank_bound : W.pwparam -> positive -> nat.
  (** Canonical payload sizes fit their width-dependent envelope. *)
  Parameter canonical_size : forall w p, canonical w p -> W.psize w p <= payload_size_bound w.
  (** Canonical payload ranks fit their parameter-dependent envelope. *)
  Parameter canonical_rank : forall q w p,
    canonical w p -> W.pwrank q w p <= payload_rank_bound q w.
  (** Payload bottom starts canonical. *)
  Parameter canonical_bot : forall w, canonical w (W.pbot w).
  (** Payload top starts canonical. *)
  Parameter canonical_top : forall w, canonical w (W.ptop w).
  (** Literal abstraction normalizes every literal. *)
  Parameter canonical_const : forall w z, canonical w (W.pconst w z).
  (** Payload join keeps canonical representations. *)
  Parameter canonical_join : forall w a b,
    canonical w a -> canonical w b -> canonical w (W.pjoin w a b).
  (** Payload meet keeps canonical representations. *)
  Parameter canonical_meet : forall w a b,
    canonical w a -> canonical w b -> canonical w (W.pmeet w a b).
  (** Payload widening keeps canonical representations. *)
  Parameter canonical_widen : forall q w a b,
    canonical w a -> canonical w b -> canonical w (W.pwiden q w a b).
  (** Payload narrowing keeps canonical representations. *)
  Parameter canonical_narrow : forall w a b,
    canonical w a -> canonical w b -> canonical w (W.pnarrow w a b).
End WORD_PAYLOAD_ENVELOPE.

Module Type WORD_TABLE_ENVELOPE (L : WORD_LANGUAGE_T) (W : WORD_PAYLOAD_T L)
    (T : WORD_TABLE_T L W) (C : WORD_PAYLOAD_ENVELOPE L W).
  (** Successful forward table entries normalize their result payload. *)
  Parameter wfwd_canonical : forall o rw xs r, T.wfwd o rw xs = Some r ->
    Forall (fun wp => C.canonical (fst wp) (snd wp)) xs -> C.canonical rw r.
  (** Successful backward table entries normalize each result at its input width. *)
  Parameter wbwd_canonical : forall o rw q xs ys, T.wbwd o rw q xs = Some ys ->
    C.canonical rw q -> Forall (fun wp => C.canonical (fst wp) (snd wp)) xs ->
    Forall2 C.canonical (map fst xs) ys.
End WORD_TABLE_ENVELOPE.

Module Type WORD_VALUE_BUDGET_LINK (L : WORD_LANGUAGE_T) (W : WORD_PAYLOAD_T L)
    (T : WORD_TABLE_T L W) (C : WORD_PAYLOAD_ENVELOPE L W)
    (B : LANG_T with Definition op := bop with Definition val := word)
    (V : VALUE_DOMAIN_T B with Definition t := tagged W.p
      with Definition wparam := W.pwparam).
  (** The concrete operator language uses the actual bit-vector evaluator. *)
  Parameter eval_bits : forall o xs, B.eval o xs = BitsLangCode.eval o xs.
  (** Tagged bottom has the common bottom constructor. *)
  Parameter bot_tag : V.bot = TBot.
  (** Tagged top accepts every width. *)
  Parameter top_tag : V.top = TAny.
  (** Tagged join applies the payload join at equal widths. *)
  Parameter join_tag : forall a b,
    V.join a b = budget_binary W.pis_bot W.pjoin a b.
  (** Tagged widening applies the payload widening at equal widths. *)
  Parameter widen_tag : forall q a b,
    V.widen q a b =
      if V.leb b a then a else budget_binary W.pis_bot (W.pwiden q) a b.
  Definition at_width (w : positive) (a : tagged W.p) : Prop :=
    match a with
    | TBot | TAny => True
    | TVal u p => u = w /\ C.canonical u p
    end.
  Definition operator_width (o : bop) (ws : list positive) (rw : positive) : Prop :=
    match o with
    | BConst w _ => ws = nil /\ rw = w
    | BOp o => Op.result_width o ws = Some rw
    end.
  (** Tagged meet intersects payloads at equal widths and treats top as unrestricted. *)
  Parameter meet_tag : forall a b,
    V.meet a b = budget_intersection W.pis_bot W.pmeet a b.
  (** Tagged narrowing applies the payload narrowing at equal widths. *)
  Parameter narrow_tag : forall a b,
    V.narrow a b = budget_intersection W.pis_bot W.pnarrow a b.
  (** A width-indexed forward result comes from a literal or a checked operator table. *)
  Parameter forward_tag : forall o xs rw p, V.forward o xs = TVal rw p ->
    (exists z, o = BConst rw z /\ xs = nil /\ p = W.pconst rw z) \/
    (exists op wps, o = BOp op /\ budget_untag xs = Some wps /\
      Op.result_width op (map fst wps) = Some rw /\
      (p = W.ptop rw \/ T.wfwd op rw wps = Some p \/ exists z, p = W.pconst rw z)).
  (** Meet keeps canonical values at the operands' expected width. *)
  Parameter meet_width : forall w a b,
    at_width w a -> at_width w b -> at_width w (V.meet a b).
  (** Narrowing keeps canonical values at the operands' expected width. *)
  Parameter narrow_width : forall w a b,
    at_width w a -> at_width w b -> at_width w (V.narrow a b).
  (** Backward transfer uses the typed operator's operand widths, including top operands. *)
  Parameter backward_width : forall o r xs ws rw,
    operator_width o ws rw -> at_width rw r -> Forall2 at_width ws xs ->
    Forall2 at_width ws (V.backward o r xs).
  (** Guard transfer keeps the typed operands' widths while refining top operands. *)
  Parameter guard_width : forall g xs ws,
    Forall2 at_width ws xs -> Forall2 at_width ws (V.guard g xs).
  (** Tagged sizes charge their width and the actual payload representation. *)
  Parameter size_tag : forall a, V.size a =
    match a with TBot | TAny => 1 | TVal w p => Pos.to_nat w + W.psize w p + 1 end.
  (** Tagged ranks add the width tag to the actual payload rank. *)
  Parameter rank_tag : forall q a, V.wrank q a =
    match a with TBot | TAny => 0 | TVal w p => 1 + W.pwrank q w p end.
End WORD_VALUE_BUDGET_LINK.

Module Type ENV_WORD_PROGRAM (X : KEY_T) (M : MAP_T X) (L : WORD_LANGUAGE_T)
    (W : WORD_PAYLOAD_T L) (B : LANG_T with Definition op := bop with Definition val := word)
    (V : VALUE_DOMAIN_T B with Definition t := tagged W.p
      with Definition wparam := W.pwparam)
    (E : ENV_ALL X M B V) (S : SYSTEM_T E).
  (* spec: variables width_of row_plan *)
  Parameter variables : S.prog -> list X.t.
  Parameter width_of : S.prog -> X.t -> positive.
  Parameter row_plan : S.prog -> S.row -> option (S.key * list (word_instruction X.t B.guard)).
  Definition typed_instruction p (i : word_instruction X.t B.guard) : Prop :=
    match i with
    | WAssign x e => In x (variables p) /\
        word_term_typed (variables p) (width_of p) e (width_of p x)
    | WHavoc x => In x (variables p)
    | WAssume _ es => Forall (fun e => exists w,
        word_term_typed (variables p) (width_of p) e w) es
    | WIdentity => True
    end.
  Definition apply_instruction (i : word_instruction X.t B.guard) (s : E.t) : E.t :=
    match i with
    | WAssign x e => E.assign x e s
    | WHavoc x => E.havoc x s
    | WAssume g es => E.assume g es s
    | WIdentity => s
    end.
  (** Listed rows use only declared variables and preserve their declared widths. *)
  Parameter instruction_typed : forall p r,
    S.wf p -> In r (S.rows p) ->
    match row_plan p r with
    | None => True
    | Some (_, instructions) => Forall (typed_instruction p) instructions
    end.
  (** Rows either seed top or fold their ordered instructions over the actual source state. *)
  Parameter row_execution : forall p r look, S.wf p -> In r (S.rows p) ->
    S.eval p r look = Some
      (match row_plan p r with
       | None => E.top
       | Some (source, instructions) =>
         fold_left (fun s i => apply_instruction i s) instructions (look source)
       end, nil).
  (** Raw environment size charges every stored payload and the map skeleton. *)
  Parameter size_environment : forall m, E.size (Reached m) =
    M.nodes m + fold_right Nat.add 0
      (map (fun code => match M.find code m with Some a => V.size a | None => 0 end)
        (M.codes m)).
  (** Unreachable environments carry no stored payloads. *)
  Parameter size_unreached : E.size Unreached = 0%nat.
  (** Unreachable environments carry no widening rank. *)
  Parameter rank_unreached : forall q, E.wrank q Unreached = 0%nat.
End ENV_WORD_PROGRAM.

Module Type ENV_BUDGET_SPEC (X : KEY_T) (M : MAP_T X) (L : WORD_LANGUAGE_T)
    (W : WORD_PAYLOAD_T L) (C : WORD_PAYLOAD_ENVELOPE L W)
    (B : LANG_T with Definition op := bop with Definition val := word)
    (V : VALUE_DOMAIN_T B with Definition t := tagged W.p
      with Definition wparam := W.pwparam)
    (E : ENV_ALL X M B V) (S : SYSTEM_T E) (P : ENV_WORD_PROGRAM X M L W B V E S).
  Definition value_inv (p : S.prog) (x : X.t) (a : V.t) : Prop :=
    match a with
    | TBot | TAny => True
    | TVal w q => w = P.width_of p x /\ C.canonical w q
    end.
  Definition inv (p : S.prog) (s : E.t) : Prop :=
    match s with
    | Unreached => True
    | Reached m => M.wf m /\
        Forall (fun xa => In (fst xa) (P.variables p) /\
          value_inv p (fst xa) (snd xa)) (M.elements m)
    end.
  Definition vsize (p : S.prog) : nat :=
    fold_right Nat.add 0 (map (fun x => X.bits x + Pos.to_nat (P.width_of p x) +
      C.payload_size_bound (P.width_of p x) + 2) (P.variables p)).
  Definition wmax (p : S.prog) (q : E.wparam) : nat :=
    fold_right Nat.add 0 (map (fun x =>
      1 + C.payload_rank_bound q (P.width_of p x)) (P.variables p)).
  Definition wunits (p : S.prog) : nat := length (P.variables p).
End ENV_BUDGET_SPEC.

(* The fallback WORKLIST_TIME.T_run_all_heads_le still requires an actual BUDGET.
   Cut-endpoint Z intervals are the separate D1 signature target reviewed in F2. *)
