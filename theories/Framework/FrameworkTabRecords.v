(** * Actual incoming and end-summary bucket invariants

    Each stored record belongs to the callee or entry bucket used by the runtime.
    For example, an incoming record is indexed by its own call target and canonical occurrence code.
    Builds on: FrameworkTabulate and the public prepared arc and map contracts. *)

From Stdlib Require Import List Bool PArith.
From Galois.Cost Require Import CostMonad CostLoop.
From Galois.Base Require Import BaseEncoding BaseEq BaseMap BaseSet BaseIndex.
From Galois.Lattice Require Import LatticeCore.
From Galois.Program Require Import ProgramIcfg.
From Galois.Framework Require Import FrameworkMicro FrameworkIfds FrameworkIde FrameworkTabulate
  FrameworkTabPaths.
Import List.ListNotations.

Module TabRecords.

(** Actual prepared arcs have exactly the observations of their own edge and fact pair. *)
Theorem arc_canonical {N E P D A F} (I : Ide.t N E P D A F) a :
  In a (Jump.arcs I) ->
  a = TabPaths.label I (Jump.edge a) (snd (Jump.source a)) (snd (Jump.target a)).
Proof.
  rewrite Jump.arcs_equation; intro Ha; apply in_flat_map in Ha.
  destruct Ha as [e [He Ha]]; apply in_flat_map in Ha.
  destruct Ha as [x [Hx Ha]]; apply in_map_iff in Ha.
  destruct Ha as [y [Heq Hy]]; subst a; reflexivity.
Qed.

(** Canonical occurrence components determine the full prepared arc, including its weight. *)
Theorem arc_key_injective {N E P D A F} (I : Ide.t N E P D A F) a b :
  In a (Jump.arcs I) -> In b (Jump.arcs I) -> Tab.arc_key a = Tab.arc_key b -> a = b.
Proof.
  intros Ha Hb Hkey.
  assert (He : Jump.edge a = Jump.edge b) by exact (f_equal fst Hkey).
  assert (Hx : snd (Jump.source a) = snd (Jump.source b))
    by exact (f_equal (fun key => fst (snd key)) Hkey).
  assert (Hy : snd (Jump.target a) = snd (Jump.target b))
    by exact (f_equal (fun key => snd (snd key)) Hkey).
  assert (Hlabels :
    TabPaths.label I (Jump.edge a) (snd (Jump.source a)) (snd (Jump.target a)) =
    TabPaths.label I (Jump.edge b) (snd (Jump.source b)) (snd (Jump.target b))).
  { rewrite He, Hx, Hy; reflexivity. }
  exact (eq_trans (arc_canonical I a Ha)
    (eq_trans Hlabels (eq_sym (arc_canonical I b Hb)))).
Qed.

(** These observers interpret the runtime's actual nested maps without constructing new records. *)
Definition callers {N E P D A F} (I : Ide.t N E P D A F)
    (s : Tab.state N E P D F) entry :=
  Map.find_or (IdeValue.key_enc I) Map.empty entry (Tab.callers s).

Definition ends {N E P D A F} (I : Ide.t N E P D A F)
    (s : Tab.state N E P D F) entry :=
  Map.find_or (IdeValue.key_enc I) Map.empty entry (Tab.ends s).

(** A caller observation is about its actual canonical code in its own callee-entry bucket. *)
Definition caller_at {N E P D A F} (I : Ide.t N E P D A F) s root a :=
  Map.get positive_encoding (encode (Tab.incoming_enc I) (root, Tab.arc_key a))
    (callers I s (Jump.target a)) = Some (root, a).

(** An end observation is about its actual canonical code in the processed entry bucket. *)
Definition end_at {N E P D A F} (I : Ide.t N E P D A F) s root a :=
  Map.get positive_encoding (encode (Tab.arc_enc I) (Tab.arc_key a)) (ends I s root) = Some a.

(** Every caller payload retains provenance, bucket ownership and its actual storage code. *)
Definition caller_owned {N E P D A F} (I : Ide.t N E P D A F) start entry code root a :=
  In root (TabPaths.roots I start) /\ In a (Jump.arcs I) /\
  (exists p, Jump.kind a = Icfg.Call p) /\ Jump.target a = entry /\
  code = encode (Tab.incoming_enc I) (root, Tab.arc_key a).

(** Every end payload retains its actual processed root, return occurrence and storage code. *)
Definition end_owned {N E P D A F} (I : Ide.t N E P D A F) start entry code a :=
  In entry (TabPaths.roots I start) /\ In a (Jump.arcs I) /\
  (exists p, Jump.kind a = Icfg.Return p) /\ code = encode (Tab.arc_enc I) (Tab.arc_key a).

(** Nested maps are well formed and their actual readable records belong to their own buckets. *)
Record valid {N E P D A F} (I : Ide.t N E P D A F) start (s : Tab.state N E P D F) : Prop := {
  callers_wf : Map.wf (IdeValue.key_enc I) (Tab.callers s);
  caller_buckets_wf : forall entry, Map.wf positive_encoding (callers I s entry);
  caller_payload : forall entry code root a,
    Map.get positive_encoding code (callers I s entry) = Some (root, a) ->
    caller_owned I start entry code root a;
  ends_wf : Map.wf (IdeValue.key_enc I) (Tab.ends s);
  end_buckets_wf : forall entry, Map.wf positive_encoding (ends I s entry);
  end_payload : forall entry code a,
    Map.get positive_encoding code (ends I s entry) = Some a ->
    end_owned I start entry code a
}.
Arguments callers_wf {N E P D A F I start s}.
Arguments caller_buckets_wf {N E P D A F I start s}.
Arguments caller_payload {N E P D A F I start s}.
Arguments ends_wf {N E P D A F I start s}.
Arguments end_buckets_wf {N E P D A F I start s}.
Arguments end_payload {N E P D A F I start s}.

Local Lemma empty_bucket {K V} (E : encoding K) key :
  Map.find_or E (@Map.empty positive V) key Map.empty = Map.empty.
Proof.
  rewrite Map.find_or_equation, Map.get_empty; reflexivity.
Qed.

Local Lemma bucket_set {K V} (E : encoding K) (m : Map.t K (Map.t positive V))
    key bucket query :
  Map.wf E m ->
  Map.find_or E Map.empty query (Map.set E key bucket m) =
    if eqb E query key then bucket else Map.find_or E Map.empty query m.
Proof.
  intro Hwf; rewrite !Map.find_or_equation, Map.get_set by exact Hwf.
  destruct (eqb E query key); reflexivity.
Qed.

(** Empty record maps satisfy ownership independently of the initial jump map and queue. *)
Theorem empty_valid {N E P D A F} (I : Ide.t N E P D A F) start js work pending :
  valid I start (Tab.State js Map.empty Map.empty work pending).
Proof.
  constructor; cbn [Tab.callers Tab.ends].
  - apply Map.wf_empty.
  - intro entry; unfold callers; cbn [Tab.callers]; rewrite empty_bucket; apply Map.wf_empty.
  - intros entry code root a Hget; unfold callers in Hget; cbn [Tab.callers] in Hget.
    rewrite empty_bucket, Map.get_empty in Hget; discriminate.
  - apply Map.wf_empty.
  - intro entry; unfold ends; cbn [Tab.ends]; rewrite empty_bucket; apply Map.wf_empty.
  - intros entry code a Hget; unfold ends in Hget; cbn [Tab.ends] in Hget.
    rewrite empty_bucket, Map.get_empty in Hget; discriminate.
Qed.

(** Changing jump values or pending work cannot change the ownership of either record map. *)
Theorem rebuild_valid {N E P D A F} (I : Ide.t N E P D A F) start s js work pending :
  valid I start s ->
  valid I start (Tab.State js (Tab.callers s) (Tab.ends s) work pending).
Proof.
  intro Hvalid; destruct Hvalid; constructor; assumption.
Qed.

(** Scheduling only changes work and pending membership. *)
Theorem schedule_valid {N E P D A F} (I : Ide.t N E P D A F) start key s :
  valid I start s -> valid I start (Tab.schedule I key s).
Proof.
  intro Hvalid; rewrite Tab.schedule_equation.
  destruct (FinSet.mem (Jump.enc I) key (Tab.pending s)); [exact Hvalid|].
  apply rebuild_valid; exact Hvalid.
Qed.

(** Joined jump updates leave all stored caller and end ownership intact. *)
Theorem update_valid {N E P D A F} (I : Ide.t N E P D A F) start key f s :
  valid I start s -> valid I start (Tab.update I key f s).
Proof.
  intro Hvalid; rewrite Tab.update_equation.
  destruct (leb (Micro.lat (Ide.micro I)) f (Jump.lookup I (Tab.jumps s) key)).
  - exact Hvalid.
  - apply schedule_valid, rebuild_valid; exact Hvalid.
Qed.

(** Return replay changes only the joined jump output and its pending key. *)
Theorem return_valid {N E P D A F} (I : Ide.t N E P D A F) start root a b s :
  valid I start s -> valid I start (Tab.return_ I root a b s).
Proof.
  intro Hvalid; rewrite Tab.return_equation.
  destruct (Cost.value (Jump.matches_c (Icfg.site_enc (Ifds.icfg (Ide.ifds I))) a b));
    [apply update_valid|]; exact Hvalid.
Qed.

(** This pure specification names the registration prefix of the actual call equation. *)
Definition registered_call {N E P D A F} (I : Ide.t N E P D A F) root a
    (s : Tab.state N E P D F) :=
  Tab.State (Tab.jumps s)
    (Map.set (IdeValue.key_enc I) (Jump.target a)
      (Map.set positive_encoding (encode (Tab.incoming_enc I) (root, Tab.arc_key a))
        (root, a) (callers I s (Jump.target a))) (Tab.callers s))
    (Tab.ends s) (Tab.work s) (Tab.pending s).

(** This pure specification names the registration prefix of the actual return equation. *)
Definition registered_end {N E P D A F} (I : Ide.t N E P D A F) root a
    (s : Tab.state N E P D F) :=
  Tab.State (Tab.jumps s) (Tab.callers s)
    (Map.set (IdeValue.key_enc I) root
      (Map.set positive_encoding (encode (Tab.arc_enc I) (Tab.arc_key a)) a (ends I s root))
      (Tab.ends s)) (Tab.work s) (Tab.pending s).

(** The call registration prefix has the actual runtime bucket observation. *)
Theorem registered_call_bucket {N E P D A F} (I : Ide.t N E P D A F) root a s entry :
  Map.wf (IdeValue.key_enc I) (Tab.callers s) ->
  callers I (registered_call I root a s) entry =
    if eqb (IdeValue.key_enc I) entry (Jump.target a) then
      Map.set positive_encoding (encode (Tab.incoming_enc I) (root, Tab.arc_key a))
        (root, a) (callers I s (Jump.target a))
    else callers I s entry.
Proof.
  intro Hwf; unfold callers, registered_call; cbn [Tab.callers].
  apply bucket_set; exact Hwf.
Qed.

(** The end registration prefix has the actual runtime bucket observation. *)
Theorem registered_end_bucket {N E P D A F} (I : Ide.t N E P D A F) root a s entry :
  Map.wf (IdeValue.key_enc I) (Tab.ends s) ->
  ends I (registered_end I root a s) entry =
    if eqb (IdeValue.key_enc I) entry root then
      Map.set positive_encoding (encode (Tab.arc_enc I) (Tab.arc_key a)) a (ends I s root)
    else ends I s entry.
Proof.
  intro Hwf; unfold ends, registered_end; cbn [Tab.ends].
  apply bucket_set; exact Hwf.
Qed.

(** Actual call registration places its canonical payload in its own callee bucket. *)
Theorem register_call_valid {N E P D A F} (I : Ide.t N E P D A F) start root a s :
  encoding_laws (IdeValue.key_enc I) -> valid I start s ->
  In root (TabPaths.roots I start) -> In a (Jump.arcs I) ->
  (exists p, Jump.kind a = Icfg.Call p) ->
  valid I start (registered_call I root a s).
Proof.
  intros HE Hvalid Hroot Ha Hkind.
  destruct Hvalid as [HCwf HCbuckets HCpayload HEwf HEbuckets HEpayload]; constructor.
  - apply Map.wf_set; exact HCwf.
  - intro entry; rewrite (registered_call_bucket I root a s entry HCwf).
    destruct (eqb (IdeValue.key_enc I) entry (Jump.target a)).
    + apply Map.wf_set; apply HCbuckets.
    + apply HCbuckets.
  - intros entry code outer call Hget.
    rewrite (registered_call_bucket I root a s entry HCwf) in Hget.
    destruct (eqb (IdeValue.key_enc I) entry (Jump.target a)) eqn:Hentry.
    + apply (eqb_true_iff (IdeValue.key_enc I) HE) in Hentry; subst entry.
      rewrite Map.get_set in Hget by apply HCbuckets.
      destruct (eqb positive_encoding code
        (encode (Tab.incoming_enc I) (root, Tab.arc_key a))) eqn:Hcode.
      * injection Hget as Houter Hcall; subst outer call.
        split; [exact Hroot|]; split; [exact Ha|]; split; [exact Hkind|].
        split; [reflexivity|apply (eqb_true_iff positive_encoding positive_encoding_laws) in Hcode].
        exact Hcode.
      * apply HCpayload with (entry := Jump.target a); exact Hget.
    + apply HCpayload with (entry := entry); exact Hget.
  - exact HEwf.
  - exact HEbuckets.
  - exact HEpayload.
Qed.

(** Actual end registration places its canonical payload in its processed entry bucket. *)
Theorem register_end_valid {N E P D A F} (I : Ide.t N E P D A F) start root a s :
  encoding_laws (IdeValue.key_enc I) -> valid I start s ->
  In root (TabPaths.roots I start) -> In a (Jump.arcs I) ->
  (exists p, Jump.kind a = Icfg.Return p) ->
  valid I start (registered_end I root a s).
Proof.
  intros HE Hvalid Hroot Ha Hkind.
  destruct Hvalid as [HCwf HCbuckets HCpayload HEwf HEbuckets HEpayload]; constructor.
  - exact HCwf.
  - exact HCbuckets.
  - exact HCpayload.
  - apply Map.wf_set; exact HEwf.
  - intro entry; rewrite (registered_end_bucket I root a s entry HEwf).
    destruct (eqb (IdeValue.key_enc I) entry root).
    + apply Map.wf_set; apply HEbuckets.
    + apply HEbuckets.
  - intros entry code ret Hget.
    rewrite (registered_end_bucket I root a s entry HEwf) in Hget.
    destruct (eqb (IdeValue.key_enc I) entry root) eqn:Hentry.
    + apply (eqb_true_iff (IdeValue.key_enc I) HE) in Hentry; subst entry.
      rewrite Map.get_set in Hget by apply HEbuckets.
      destruct (eqb positive_encoding code (encode (Tab.arc_enc I) (Tab.arc_key a))) eqn:Hcode.
      * injection Hget as Hret; subst ret.
        split; [exact Hroot|]; split; [exact Ha|]; split; [exact Hkind|].
        apply (eqb_true_iff positive_encoding positive_encoding_laws) in Hcode; exact Hcode.
      * apply HEpayload with (entry := root); exact Hget.
    + apply HEpayload with (entry := entry); exact Hget.
Qed.

Local Lemma fold_valid {X S} (P : S -> Prop) (f : S -> X -> S) xs s :
  (forall s x, P s -> In x xs -> P (f s x)) -> P s -> P (fold_left f xs s).
Proof.
  revert s; induction xs as [|x xs IH]; intros s Hstep Hs; cbn [fold_left].
  - exact Hs.
  - apply IH.
    + intros t y Ht Hy; apply Hstep; [exact Ht|right; exact Hy].
    + apply Hstep; [exact Hs|left; reflexivity].
Qed.

(** Actual call processing keeps bucket ownership while replaying every known end. *)
Theorem call_valid {N E P D A F} (I : Ide.t N E P D A F) start root a s :
  encoding_laws (IdeValue.key_enc I) -> valid I start s ->
  In root (TabPaths.roots I start) -> In a (Jump.arcs I) ->
  (exists p, Jump.kind a = Icfg.Call p) ->
  valid I start (Cost.value (Tab.call_c I root a s)).
Proof.
  intros HE Hvalid Hroot Ha Hkind; rewrite Tab.call_equation.
  apply fold_valid.
  - intros t kv Ht Hkv; apply return_valid; exact Ht.
  - apply register_call_valid; assumption.
Qed.

(** Actual end processing keeps ownership while replaying every registered caller. *)
Theorem end_valid {N E P D A F} (I : Ide.t N E P D A F) start root a s :
  encoding_laws (IdeValue.key_enc I) -> valid I start s ->
  In root (TabPaths.roots I start) -> In a (Jump.arcs I) ->
  (exists p, Jump.kind a = Icfg.Return p) ->
  valid I start (Cost.value (Tab.end_c I root a s)).
Proof.
  intros HE Hvalid Hroot Ha Hkind; rewrite Tab.end_equation.
  apply fold_valid.
  - intros t kv Ht Hkv; apply return_valid; exact Ht.
  - apply register_end_valid; assumption.
Qed.

(** Arc dispatch preserves exact caller/end ownership on actual prepared roots and arcs. *)
Theorem arc_valid {N E P D A F} (I : Ide.t N E P D A F) start root a s :
  encoding_laws (IdeValue.key_enc I) -> valid I start s ->
  In root (TabPaths.roots I start) -> In a (Jump.arcs I) ->
  valid I start (Cost.value (Tab.arc_c I root a s)).
Proof.
  intros HE Hvalid Hroot Ha; rewrite Tab.arc_equation.
  destruct (Jump.kind a) as [|p|p] eqn:Hkind.
  - apply update_valid; exact Hvalid.
  - apply call_valid with (start := start); try assumption; exists p; exact Hkind.
  - apply end_valid with (start := start); try assumption; exists p; exact Hkind.
Qed.

(** Pure equality of both record maps does not constrain jumps or the worklist. *)
Definition same {N E P D F} (before after : Tab.state N E P D F) :=
  Tab.callers after = Tab.callers before /\ Tab.ends after = Tab.ends before.

(** Scheduling retains both nested record maps exactly. *)
Theorem schedule_same {N E P D A F} (I : Ide.t N E P D A F) key s :
  same s (Tab.schedule I key s).
Proof.
  rewrite Tab.schedule_equation.
  destruct (FinSet.mem (Jump.enc I) key (Tab.pending s)); split; reflexivity.
Qed.

(** Joined updates retain both nested record maps exactly. *)
Theorem update_same {N E P D A F} (I : Ide.t N E P D A F) key f s :
  same s (Tab.update I key f s).
Proof.
  rewrite Tab.update_equation.
  destruct (leb (Micro.lat (Ide.micro I)) f (Jump.lookup I (Tab.jumps s) key)).
  - split; reflexivity.
  - rewrite Tab.schedule_equation; cbn [Tab.pending Tab.callers Tab.ends].
    destruct (FinSet.mem (Jump.enc I) key (Tab.pending s)); split; reflexivity.
Qed.

(** Return replay leaves all incoming and end-summary records unchanged. *)
Theorem return_same {N E P D A F} (I : Ide.t N E P D A F) root a b s :
  same s (Tab.return_ I root a b s).
Proof.
  rewrite Tab.return_equation.
  destruct (Cost.value (Jump.matches_c (Icfg.site_enc (Ifds.icfg (Ide.ifds I))) a b)).
  - apply update_same.
  - split; reflexivity.
Qed.

Local Lemma fold_same {N E P D F X} (f : Tab.state N E P D F -> X -> Tab.state N E P D F)
    xs s :
  (forall t x, same t (f t x)) -> same s (fold_left f xs s).
Proof.
  intro Hstep; revert s; induction xs as [|x xs IH]; intro s; cbn [fold_left].
  - split; reflexivity.
  - destruct (IH (f s x)) as [HC HE]; destruct (Hstep s x) as [HCstep HEstep].
    split; [rewrite HC, HCstep|rewrite HE, HEstep]; reflexivity.
Qed.

Local Lemma callers_same {N E P D A F} (I : Ide.t N E P D A F) before after entry :
  same before after -> callers I after entry = callers I before entry.
Proof.
  intros [HC HE]; unfold callers; rewrite HC; reflexivity.
Qed.

Local Lemma ends_same {N E P D A F} (I : Ide.t N E P D A F) before after entry :
  same before after -> ends I after entry = ends I before entry.
Proof.
  intros [HC HE]; unfold ends; rewrite HE; reflexivity.
Qed.

(** Complete call processing changes exactly the addressed caller bucket. *)
Theorem call_buckets {N E P D A F} (I : Ide.t N E P D A F) start root a s entry :
  valid I start s ->
  callers I (Cost.value (Tab.call_c I root a s)) entry =
    (if eqb (IdeValue.key_enc I) entry (Jump.target a) then
      Map.set positive_encoding (encode (Tab.incoming_enc I) (root, Tab.arc_key a))
        (root, a) (callers I s (Jump.target a))
    else callers I s entry) /\
  ends I (Cost.value (Tab.call_c I root a s)) entry = ends I s entry.
Proof.
  intro Hvalid; rewrite Tab.call_equation; cbn zeta.
  pose proof (fold_same (fun t kv => Tab.return_ I root a (snd kv) t)
    (Map.elements (ends I s (Jump.target a))) (registered_call I root a s)
    (fun t kv => return_same I root a (snd kv) t)) as Hsame.
  split.
  - transitivity (callers I (registered_call I root a s) entry).
    + exact (callers_same I _ _ entry Hsame).
    + apply registered_call_bucket; exact (callers_wf Hvalid).
  - transitivity (ends I (registered_call I root a s) entry).
    + exact (ends_same I _ _ entry Hsame).
    + reflexivity.
Qed.

(** Complete end processing changes exactly the addressed end-summary bucket. *)
Theorem end_buckets {N E P D A F} (I : Ide.t N E P D A F) start root a s entry :
  valid I start s ->
  callers I (Cost.value (Tab.end_c I root a s)) entry = callers I s entry /\
  ends I (Cost.value (Tab.end_c I root a s)) entry =
    (if eqb (IdeValue.key_enc I) entry root then
      Map.set positive_encoding (encode (Tab.arc_enc I) (Tab.arc_key a)) a (ends I s root)
    else ends I s entry).
Proof.
  intro Hvalid; rewrite Tab.end_equation; cbn zeta.
  pose proof (fold_same (fun t kv =>
    Tab.return_ I (fst (snd kv)) (snd (snd kv)) a t)
    (Map.elements (callers I s root)) (registered_end I root a s)
    (fun t kv => return_same I (fst (snd kv)) (snd (snd kv)) a t)) as Hsame.
  split.
  - transitivity (callers I (registered_end I root a s) entry).
    + exact (callers_same I _ _ entry Hsame).
    + reflexivity.
  - transitivity (ends I (registered_end I root a s) entry).
    + exact (ends_same I _ _ entry Hsame).
    + apply registered_end_bucket; exact (ends_wf Hvalid).
Qed.

(** The actual call pass always installs its own canonical incoming record. *)
Theorem call_installs {N E P D A F} (I : Ide.t N E P D A F) start root a s :
  valid I start s -> caller_at I (Cost.value (Tab.call_c I root a s)) root a.
Proof.
  intro Hvalid; unfold caller_at.
  rewrite (proj1 (call_buckets I start root a s (Jump.target a) Hvalid)), eqb_refl.
  apply Map.get_set_same; exact (caller_buckets_wf Hvalid _).
Qed.

(** The actual end pass always installs its own canonical end-summary record. *)
Theorem end_installs {N E P D A F} (I : Ide.t N E P D A F) start root a s :
  valid I start s -> end_at I (Cost.value (Tab.end_c I root a s)) root a.
Proof.
  intro Hvalid; unfold end_at.
  rewrite (proj2 (end_buckets I start root a s root Hvalid)), eqb_refl.
  apply Map.get_set_same; exact (end_buckets_wf Hvalid _).
Qed.

(** Installing a caller cannot erase any existing actual caller with a distinct occurrence. *)
Theorem call_keeps_caller {N E P D A F} (I : Ide.t N E P D A F)
    start root a s oldroot oldcall :
  encoding_laws (IdeValue.key_enc I) -> encoding_laws (Tab.incoming_enc I) ->
  valid I start s -> In a (Jump.arcs I) -> caller_at I s oldroot oldcall ->
  caller_at I (Cost.value (Tab.call_c I root a s)) oldroot oldcall.
Proof.
  intros HE HI Hvalid Ha Hold; unfold caller_at in *.
  pose proof (caller_payload Hvalid _ _ _ _ Hold) as Howned.
  destruct Howned as [Hroot [Holdarc Hrest]].
  rewrite (proj1 (call_buckets I start root a s (Jump.target oldcall) Hvalid)).
  destruct (eqb (IdeValue.key_enc I) (Jump.target oldcall) (Jump.target a)) eqn:Hentry;
    [|exact Hold].
  apply (eqb_true_iff (IdeValue.key_enc I) HE) in Hentry.
  rewrite Map.get_set by exact (caller_buckets_wf Hvalid _).
  destruct (eqb positive_encoding
    (encode (Tab.incoming_enc I) (oldroot, Tab.arc_key oldcall))
    (encode (Tab.incoming_enc I) (root, Tab.arc_key a))) eqn:Hcode.
  - apply (eqb_true_iff positive_encoding positive_encoding_laws) in Hcode.
    apply (encode_injective HI) in Hcode.
    assert (Houter : oldroot = root) by exact (f_equal fst Hcode).
    assert (Hkey : Tab.arc_key oldcall = Tab.arc_key a) by exact (f_equal snd Hcode).
    subst oldroot.
    apply (arc_key_injective I oldcall a Holdarc Ha) in Hkey; subst oldcall; reflexivity.
  - rewrite <- Hentry; exact Hold.
Qed.

(** Installing an end summary cannot erase any existing actual end occurrence. *)
Theorem end_keeps_end {N E P D A F} (I : Ide.t N E P D A F)
    start root a s oldroot oldend :
  encoding_laws (IdeValue.key_enc I) -> encoding_laws (Tab.arc_enc I) ->
  valid I start s -> In a (Jump.arcs I) -> end_at I s oldroot oldend ->
  end_at I (Cost.value (Tab.end_c I root a s)) oldroot oldend.
Proof.
  intros HE HA Hvalid Ha Hold; unfold end_at in *.
  pose proof (end_payload Hvalid _ _ _ Hold) as Howned.
  destruct Howned as [Hroot [Holdarc Hrest]].
  rewrite (proj2 (end_buckets I start root a s oldroot Hvalid)).
  destruct (eqb (IdeValue.key_enc I) oldroot root) eqn:Hentry; [|exact Hold].
  apply (eqb_true_iff (IdeValue.key_enc I) HE) in Hentry; subst oldroot.
  rewrite Map.get_set by exact (end_buckets_wf Hvalid _).
  destruct (eqb positive_encoding (encode (Tab.arc_enc I) (Tab.arc_key oldend))
    (encode (Tab.arc_enc I) (Tab.arc_key a))) eqn:Hcode.
  - apply (eqb_true_iff positive_encoding positive_encoding_laws) in Hcode.
    apply (encode_injective HA) in Hcode.
    apply (arc_key_injective I oldend a Holdarc Ha) in Hcode; subst oldend; reflexivity.
  - exact Hold.
Qed.

(** Call processing never changes end-summary observations. *)
Theorem call_keeps_end {N E P D A F} (I : Ide.t N E P D A F)
    start root a s oldroot oldend :
  valid I start s -> end_at I s oldroot oldend ->
  end_at I (Cost.value (Tab.call_c I root a s)) oldroot oldend.
Proof.
  intros Hvalid Hold; unfold end_at in *.
  rewrite (proj2 (call_buckets I start root a s oldroot Hvalid)); exact Hold.
Qed.

(** End processing never changes incoming-caller observations. *)
Theorem end_keeps_caller {N E P D A F} (I : Ide.t N E P D A F)
    start root a s oldroot oldcall :
  valid I start s -> caller_at I s oldroot oldcall ->
  caller_at I (Cost.value (Tab.end_c I root a s)) oldroot oldcall.
Proof.
  intros Hvalid Hold; unfold caller_at in *.
  rewrite (proj1 (end_buckets I start root a s (Jump.target oldcall) Hvalid)); exact Hold.
Qed.

(** A newly observed caller was already present or is exactly the call just registered. *)
Theorem call_new_or_old {N E P D A F} (I : Ide.t N E P D A F)
    start root a s oldroot oldcall :
  encoding_laws (IdeValue.key_enc I) -> valid I start s ->
  caller_at I (Cost.value (Tab.call_c I root a s)) oldroot oldcall ->
  caller_at I s oldroot oldcall \/ (oldroot = root /\ oldcall = a).
Proof.
  intros HV Hvalid Hget; unfold caller_at in Hget.
  rewrite (proj1 (call_buckets I start root a s (Jump.target oldcall) Hvalid)) in Hget.
  destruct (eqb (IdeValue.key_enc I) (Jump.target oldcall) (Jump.target a)) eqn:Hentry.
  - apply (eqb_true_iff (IdeValue.key_enc I) HV) in Hentry.
    rewrite Map.get_set in Hget by exact (caller_buckets_wf Hvalid _).
    destruct (eqb positive_encoding
      (encode (Tab.incoming_enc I) (oldroot, Tab.arc_key oldcall))
      (encode (Tab.incoming_enc I) (root, Tab.arc_key a))).
    + assert (Hpair : (root, a) = (oldroot, oldcall)) by congruence.
      right; split; [exact (eq_sym (f_equal fst Hpair))|exact (eq_sym (f_equal snd Hpair))].
    + left; unfold caller_at; rewrite Hentry; exact Hget.
  - left; exact Hget.
Qed.

(** A newly observed end was already present or is exactly the end just registered. *)
Theorem end_new_or_old {N E P D A F} (I : Ide.t N E P D A F)
    start root a s oldroot oldend :
  encoding_laws (IdeValue.key_enc I) -> valid I start s ->
  end_at I (Cost.value (Tab.end_c I root a s)) oldroot oldend ->
  end_at I s oldroot oldend \/ (oldroot = root /\ oldend = a).
Proof.
  intros HV Hvalid Hget; unfold end_at in Hget.
  rewrite (proj2 (end_buckets I start root a s oldroot Hvalid)) in Hget.
  destruct (eqb (IdeValue.key_enc I) oldroot root) eqn:Hentry.
  - apply (eqb_true_iff (IdeValue.key_enc I) HV) in Hentry; subst oldroot.
    rewrite Map.get_set in Hget by exact (end_buckets_wf Hvalid _).
    destruct (eqb positive_encoding (encode (Tab.arc_enc I) (Tab.arc_key oldend))
      (encode (Tab.arc_enc I) (Tab.arc_key a))).
    + right; split; [reflexivity|congruence].
    + left; exact Hget.
  - left; exact Hget.
Qed.

(** Exact map retention preserves every canonical caller observation. *)
Theorem same_caller {N E P D A F} (I : Ide.t N E P D A F) before after root a :
  same before after -> caller_at I before root a -> caller_at I after root a.
Proof.
  intros Hsame Hold; unfold caller_at in *.
  rewrite (callers_same I before after (Jump.target a) Hsame); exact Hold.
Qed.

(** Exact map retention preserves every canonical end observation. *)
Theorem same_end {N E P D A F} (I : Ide.t N E P D A F) before after root a :
  same before after -> end_at I before root a -> end_at I after root a.
Proof.
  intros Hsame Hold; unfold end_at in *.
  rewrite (ends_same I before after root Hsame); exact Hold.
Qed.

(** Actual arc processing retains every canonical caller occurrence under lawful occurrence codes. *)
Theorem arc_keeps_caller {N E P D A F} (I : Ide.t N E P D A F)
    start root a s oldroot oldcall :
  encoding_laws (IdeValue.key_enc I) -> encoding_laws (Tab.incoming_enc I) ->
  valid I start s -> In a (Jump.arcs I) -> caller_at I s oldroot oldcall ->
  caller_at I (Cost.value (Tab.arc_c I root a s)) oldroot oldcall.
Proof.
  intros HV HI Hvalid Ha Hold; rewrite Tab.arc_equation; destruct (Jump.kind a).
  - apply same_caller with (before := s); [apply update_same|exact Hold].
  - apply call_keeps_caller with (start := start); assumption.
  - apply end_keeps_caller with (start := start); assumption.
Qed.

(** Actual arc processing retains every canonical end occurrence under lawful occurrence codes. *)
Theorem arc_keeps_end {N E P D A F} (I : Ide.t N E P D A F)
    start root a s oldroot oldend :
  encoding_laws (IdeValue.key_enc I) -> encoding_laws (Tab.arc_enc I) ->
  valid I start s -> In a (Jump.arcs I) -> end_at I s oldroot oldend ->
  end_at I (Cost.value (Tab.arc_c I root a s)) oldroot oldend.
Proof.
  intros HV HA Hvalid Ha Hold; rewrite Tab.arc_equation; destruct (Jump.kind a).
  - apply same_end with (before := s); [apply update_same|exact Hold].
  - apply call_keeps_end with (start := start); assumption.
  - apply end_keeps_end with (start := start); assumption.
Qed.

(** Enumerating a caller bucket exposes the same owned records as canonical map lookup. *)
Theorem caller_element {N E P D A F} (I : Ide.t N E P D A F) start s entry code root a :
  valid I start s -> In (code, (root, a)) (Map.elements (callers I s entry)) ->
  caller_owned I start entry code root a.
Proof.
  intros Hvalid Hin; apply (caller_payload Hvalid entry code root a).
  apply (proj1 (Map.elements_spec positive_encoding positive_encoding_laws
    code (root, a) (callers I s entry) (caller_buckets_wf Hvalid entry))); exact Hin.
Qed.

(** Enumerating an end bucket exposes the same owned records as canonical map lookup. *)
Theorem end_element {N E P D A F} (I : Ide.t N E P D A F) start s entry code a :
  valid I start s -> In (code, a) (Map.elements (ends I s entry)) ->
  end_owned I start entry code a.
Proof.
  intros Hvalid Hin; apply (end_payload Hvalid entry code a).
  apply (proj1 (Map.elements_spec positive_encoding positive_encoding_laws
    code a (ends I s entry) (end_buckets_wf Hvalid entry))); exact Hin.
Qed.

(** The root of every pending jump key is an actual prepared entry root. *)
Definition work_roots {N E P D A F} (I : Ide.t N E P D A F) start
    (s : Tab.state N E P D F) :=
  forall key, In key (Tab.work s) -> In (fst key) (TabPaths.roots I start).

(** Ownership and work-root support are maintained together by the specialized engine. *)
Definition invariant {N E P D A F} (I : Ide.t N E P D A F) start s :=
  valid I start s /\ work_roots I start s.

Local Lemma schedule_roots {N E P D A F} (I : Ide.t N E P D A F) start key s :
  work_roots I start s -> In (fst key) (TabPaths.roots I start) ->
  work_roots I start (Tab.schedule I key s).
Proof.
  intros Hwork Hroot; rewrite Tab.schedule_equation.
  destruct (FinSet.mem (Jump.enc I) key (Tab.pending s)); [exact Hwork|].
  intros other [Heq|Hin]; [subst other; exact Hroot|apply Hwork; exact Hin].
Qed.

Local Lemma update_roots {N E P D A F} (I : Ide.t N E P D A F) start key f s :
  work_roots I start s -> In (fst key) (TabPaths.roots I start) ->
  work_roots I start (Tab.update I key f s).
Proof.
  intros Hwork Hroot; rewrite Tab.update_equation.
  destruct (leb (Micro.lat (Ide.micro I)) f (Jump.lookup I (Tab.jumps s) key));
    [exact Hwork|].
  apply schedule_roots; [exact Hwork|exact Hroot].
Qed.

Local Lemma return_roots {N E P D A F} (I : Ide.t N E P D A F) start root a b s :
  work_roots I start s -> In root (TabPaths.roots I start) ->
  work_roots I start (Tab.return_ I root a b s).
Proof.
  intros Hwork Hroot; rewrite Tab.return_equation.
  destruct (Cost.value (Jump.matches_c (Icfg.site_enc (Ifds.icfg (Ide.ifds I))) a b));
    [apply update_roots|]; assumption.
Qed.

Local Lemma call_roots {N E P D A F} (I : Ide.t N E P D A F) start root a s :
  work_roots I start s -> In root (TabPaths.roots I start) ->
  work_roots I start (Cost.value (Tab.call_c I root a s)).
Proof.
  intros Hwork Hroot; rewrite Tab.call_equation; apply fold_valid.
  - intros t kv Ht Hkv; apply return_roots; assumption.
  - exact Hwork.
Qed.

Local Lemma end_roots {N E P D A F} (I : Ide.t N E P D A F) start root a s :
  valid I start s -> work_roots I start s ->
  work_roots I start (Cost.value (Tab.end_c I root a s)).
Proof.
  intros Hvalid Hwork; rewrite Tab.end_equation; apply fold_valid.
  - intros t [code [outer call]] Ht Hin; cbn [fst snd].
    assert (Hget : Map.get positive_encoding code (callers I s root) = Some (outer, call)).
    { apply (proj1 (Map.elements_spec positive_encoding positive_encoding_laws
        code (outer, call) (callers I s root) (caller_buckets_wf Hvalid root))); exact Hin. }
    pose proof (caller_payload Hvalid root code outer call Hget) as Howned.
    apply return_roots; [exact Ht|exact (proj1 Howned)].
  - exact Hwork.
Qed.

(** Actual arc processing preserves bucket ownership and the prepared roots of all work. *)
Theorem arc_invariant {N E P D A F} (I : Ide.t N E P D A F) start root a s :
  encoding_laws (IdeValue.key_enc I) -> invariant I start s ->
  In root (TabPaths.roots I start) -> In a (Jump.arcs I) ->
  invariant I start (Cost.value (Tab.arc_c I root a s)).
Proof.
  intros HE [Hvalid Hwork] Hroot Ha; split.
  - apply arc_valid with (start := start); assumption.
  - rewrite Tab.arc_equation; destruct (Jump.kind a) as [|p|p] eqn:Hkind.
    + apply update_roots; assumption.
    + apply call_roots; assumption.
    + apply end_roots; assumption.
Qed.

(** Every conservative inventory key has an actual prepared entry root. *)
Theorem inventory_root {N E P D A F} (I : Ide.t N E P D A F) start key :
  In key (Tab.inventory (Tab.prepare I start)) -> In (fst key) (TabPaths.roots I start).
Proof.
  rewrite Tab.prepare_equation; cbn [Tab.inventory].
  intro Hin; apply in_flat_map in Hin; destruct Hin as [root [Hroot Hin]].
  apply in_map_iff in Hin; destruct Hin as [v [Heq Hv]]; subst key; exact Hroot.
Qed.

(** Every source-index observation is an actual prepared exploded arc. *)
Theorem outgoing_member {N E P D A F} (I : Ide.t N E P D A F) start v a :
  In a (Index.find (IdeValue.key_enc I) v (Tab.outgoing (Tab.prepare I start))) ->
  In a (Jump.arcs I).
Proof.
  rewrite Tab.prepare_equation; cbn [Tab.outgoing]; rewrite Index.find_group_by.
  intro Hin; apply filter_In in Hin; exact (proj1 Hin).
Qed.

Section Run.
Context {N E P D A F} (I : Ide.t N E P D A F) (start : N).
Context (HE : encoding_laws (IdeValue.key_enc I)).

(** Initialization establishes owned empty buckets and prepared work roots without semantic laws. *)
Theorem initial_invariant : invariant I start (Tab.initial I (Tab.prepare I start)).
Proof.
  rewrite Tab.initial_equation; apply fold_valid.
  - intros s root [Hvalid Hwork] Hroot.
    assert (Hr : In root (TabPaths.roots I start)).
    { rewrite Tab.prepare_equation in Hroot; exact Hroot. }
    split; [apply update_valid; exact Hvalid|apply update_roots; assumption].
  - apply fold_valid.
    + intros s key [Hvalid Hwork] Hkey; split.
      * apply schedule_valid; exact Hvalid.
      * apply schedule_roots; [exact Hwork|apply inventory_root; exact Hkey].
    + split; [apply empty_valid|intros key Hin; inversion Hin].
Qed.

(** Each raw callback preserves actual bucket ownership in both its possible outcomes. *)
Theorem step_invariant s :
  invariant I start s ->
  match Tab.step I (Tab.prepare I start) s with
  | inl next | inr next => invariant I start next
  end.
Proof.
  intros [Hvalid Hwork]; rewrite Tab.tabulate_equation.
  destruct (Tab.work s) as [|[root v] rest] eqn:Hqueue.
  - split; assumption.
  - apply fold_valid.
    + intros t a Ht Ha; apply arc_invariant with (start := start); try assumption.
      * apply (Hwork (root, v)); rewrite Hqueue; left; reflexivity.
      * apply outgoing_member with (start := start) (v := v); exact Ha.
    + split; [apply rebuild_valid; exact Hvalid|].
      intros key Hkey; apply Hwork; rewrite Hqueue; right; exact Hkey.
Qed.

(** Every actual raw state, including exhaustion, retains exact bucket ownership and root support. *)
Theorem raw_invariant fuel :
  match Tab.raw I start fuel with
  | inl s | inr s => invariant I start s
  end.
Proof.
  rewrite Tab.raw_equation.
  pose proof (iterate_value (Tab.step_c I (Tab.prepare I start)) fuel
    (Tab.initial I (Tab.prepare I start))) as Hrun.
  assert (Hpreserved : forall n s result,
    runs (Tab.step_c I (Tab.prepare I start)) n s result ->
    invariant I start s ->
    match result with
    | inl next | inr next => invariant I start next
    end).
  { intros n s result Hr; induction Hr as [s|n s r Hstop|n s next result Hnext Hr IH];
      intro Hinv.
    - exact Hinv.
    - pose proof (step_invariant s Hinv) as Hstep.
      rewrite Tab.step_c_value in Hstop; rewrite Hstop in Hstep; exact Hstep.
    - apply IH; pose proof (step_invariant s Hinv) as Hstep.
      rewrite Tab.step_c_value in Hnext; rewrite Hnext in Hstep; exact Hstep. }
  exact (Hpreserved _ _ _ Hrun initial_invariant).
Qed.

End Run.

End TabRecords.
