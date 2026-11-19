(** * Natural numbers, characters, pairs, options and lists as values

    Programs derived with [Egglog] over the value types [nat] and [ascii], which [EncodeNat.v]
    and [EncodeAscii.v] register, and over pairs, options and lists of value types, whose
    encoders the command builds from the encoders of their parts. Such values are relation
    indices, input columns and primitive arguments, and an input constructor may hold a list.
    The tests read the rows of a run through the encoders.
    For example, the input [Job 2 [1]] says that the job 2 waits for the job 1, and the run of
    [Jobs] derives the row of [blocked] for 2 and 1 with the primitive [waits_for].

    Groups:
    - [EncoderTests] The stock encoders and the encoders of pairs, options and lists.
    - [NaturalTests] A relation over [nat] with an equation premise.
    - [CharacterTests] A relation over [ascii].
    - [PairTests] A relation whose indices and an input column are pairs of integers.
    - [OptionTests] Relations over options, with a literal [None] in a premise.
    - [ListValueTests] Input constructors that hold lists, and list indices and primitives.
    - [GlueTests] The generated lemmas in both directions.
    - [RejectionTests] The command stops at values that it cannot read.

    Builds on: the derive command, the encoders, the runner and the engine. *)

From Stdlib Require Import List PArith NArith ZArith Ascii String.
From Galois.Base Require Import Key.
From Galois.Egglog Require Import ValueSig Syntax Model Index Join Database Run.
From Galois.Front Require Import Spec RunnerSig Runner Encode EncodeNat EncodeAscii Derive.
Import List.ListNotations.

(** * Fixtures *)

(** The point with its coordinates swapped. *)
Definition swap (p : Z * Z) : Z * Z := (snd p, fst p).

(** The integer of an entry, or zero for no entry. *)
Definition or_zero (o : option Z) : Z :=
  match o with
  | Some z => z
  | None => 0%Z
  end.

(** Whether a job waits for the job [d] among the jobs [ds]. *)
Definition waits_for (d : positive) (ds : list positive) : bool := existsb (Pos.eqb d) ds.

(** The jobs in the reverse order. *)
Definition reversed (ds : list positive) : list positive := rev ds.

(** Primitives over natural numbers, pairs, options and lists. *)
Egglog Primitives Ops Nat.add swap or_zero waits_for reversed.

(** Values are positives, and the primitive function is the one that [Ops] generated. *)
Module OpsValue <: VALUE_OPS.
  Include PosKeyCode.
  Definition prim := Ops.prim.
  Definition merge (_ : positive) := Pos.max.
End OpsValue.

Module OpsIndex := IndexCode OpsValue.
Module OpsJoin := JoinCode OpsValue OpsIndex.
Module OpsDatabase := DatabaseCode OpsValue OpsIndex.
Module OpsRun := RunCode OpsValue OpsIndex OpsJoin OpsDatabase.
Module OpsRunner := RunnerCode OpsValue OpsIndex OpsJoin OpsDatabase OpsRun.

(** Saturation stops after at most 10 iterations and allocates at most 1000 identifiers. *)
Definition ops_limits : limits := Limits 10%N 1000%N.

(** [counted steps x y] says that the steps of [steps] lead from [x] to [y], and each step
    [(x, k)] adds [k]. *)
Inductive counted (steps : list (nat * nat)) : nat -> nat -> Prop :=
  | counted_step x k y : In (x, k) steps -> Nat.add x k = y -> counted steps x y
  | counted_more x y k z : counted steps x y -> In (y, k) steps -> Nat.add y k = z ->
      counted steps x z.

Egglog Counts from counted with Ops.

(** [follows links a b] says that the links lead from the character [a] to [b]. *)
Inductive follows (links : list (ascii * ascii)) : ascii -> ascii -> Prop :=
  | follows_link a b : In (a, b) links -> follows links a b
  | follows_more a b c : follows links a b -> In (b, c) links -> follows links a c.

Egglog Follows from follows.

(** [mirrored points p q] says that [q] swaps the coordinates of a point [p] of [points],
    which holds each point with a tag. *)
Inductive mirrored (points : list ((Z * Z) * positive)) : Z * Z -> Z * Z -> Prop :=
  | mirrored_point p tag q : In (p, tag) points -> swap p = q -> mirrored points p q.

Egglog Mirrors from mirrored with Ops.

(** [entry table k o] says that [table] holds the entry [o] at the key [k]. *)
Inductive entry (table : list (positive * option Z)) : positive -> option Z -> Prop :=
  | entry_in k o : In (k, o) table -> entry table k o.

(** [missing table k] says that [table] holds no value at the key [k]. *)
Inductive missing (table : list (positive * option Z)) : positive -> Prop :=
  | missing_in k : In (k, None) table -> missing table k.

(** [defaulted table k z] says that the entry at [k] is [z], or zero for no value. *)
Inductive defaulted (table : list (positive * option Z)) : positive -> Z -> Prop :=
  | defaulted_entry k o z : entry table k o -> or_zero o = z -> defaulted table k z.

Egglog Entries from entry missing defaulted with Ops.

(** A job with its number and the numbers of the jobs that it waits for. *)
Inductive job : Type :=
  | Job (id : positive) (deps : list positive).

(** [waits jobs i ds] says that the job [i] waits for the jobs [ds]. *)
Inductive waits (jobs : list job) : positive -> list positive -> Prop :=
  | waits_job i ds : In (Job i ds) jobs -> waits jobs i ds.

(** [idle jobs i] says that the job [i] waits for no job. *)
Inductive idle (jobs : list job) : positive -> Prop :=
  | idle_job i : In (Job i []) jobs -> idle jobs i.

(** [blocked jobs i d] says that the job [i] waits for the job [d]. *)
Inductive blocked (jobs : list job) : positive -> positive -> Prop :=
  | blocked_on i ds d es : In (Job i ds) jobs -> In (Job d es) jobs -> waits_for d ds = true ->
      blocked jobs i d.

(** [backwards jobs i rs] says that [rs] lists the jobs that [i] waits for in the reverse
    order. *)
Inductive backwards (jobs : list job) : positive -> list positive -> Prop :=
  | backwards_of i ds rs : waits jobs i ds -> reversed ds = rs -> backwards jobs i rs.

Egglog Jobs from waits idle blocked backwards with Ops.

(** * Encoders *)

Module EncoderTests.

  Local Open Scope positive_scope.

  (** The natural number [n] is the positive [n + 1]. *)
  Example natural_is_its_successor :
    NatEncode.encode 4 = 5.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Every positive decodes to a natural number. *)
  Example every_positive_is_a_natural :
    NatEncode.decode 1 = Some 0%nat.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A character is the string that holds it alone. *)
  Example character_is_a_string :
    AsciiEncode.encode "a"%char = StringEncode.encode "a"%string.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The encoding of a string of two characters is no character. *)
  Example longer_string_is_no_character :
    AsciiEncode.decode (StringEncode.encode "ab"%string) = None.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** Pairs that differ in one side have different encodings. *)
  Example pairs_are_told_apart :
    encode_pair ZEncode.encode ZEncode.encode (1%Z, 2%Z) <>
      encode_pair ZEncode.encode ZEncode.encode (2%Z, 1%Z).
  Proof.
    vm_compute. discriminate.
  Qed.

  (** The empty list and the list of one zero have different encodings. *)
  Example list_lengths_are_told_apart :
    encode_list ZEncode.encode [] <> encode_list ZEncode.encode [0%Z].
  Proof.
    vm_compute. discriminate.
  Qed.

  (** A list of pairs of options decodes back to itself. *)
  Example nested_value_decodes_back :
    let coder := encode_list (encode_pair (encode_option ZEncode.encode) BoolEncode.encode) in
    let reader := decode_list (decode_pair (decode_option ZEncode.decode) BoolEncode.decode) in
    reader (coder [(Some (-3)%Z, true); (None, false)]) =
      Some [(Some (-3)%Z, true); (None, false)].
  Proof.
    vm_compute. reflexivity.
  Qed.

End EncoderTests.

(** * Natural numbers *)

Module NaturalTests.

  (** Two steps, from 0 by 2 and from 2 by 3. *)
  Definition two_steps : list (nat * nat) := [(0, 2); (2, 3)]%nat.

  (** The database after running [Counts] on the two steps. *)
  Definition counted_result : OpsDatabase.t :=
    snd (OpsRunner.solve Counts.program (Counts.facts two_steps) ops_limits).

  (** Whether the database has the row of [counted] for two natural numbers. *)
  Definition counts (x y : nat) : bool :=
    OpsRunner.holds Counts.counted_code [NatEncode.encode x; NatEncode.encode y]
      counted_result.

  (** Two steps lead from 0 to 5. *)
  Example two_steps_add_up :
    counts 0 5 = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** No step leads from 0 to 3. *)
  Example unreached_number_has_no_row :
    counts 0 3 = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End NaturalTests.

(** * Characters *)

Module CharacterTests.

  Local Open Scope char_scope.

  (** Links from a to b and from b to c. *)
  Definition two_links : list (ascii * ascii) := [("a", "b"); ("b", "c")].

  (** The database after running [Follows] on the two links. *)
  Definition follows_result : OpsDatabase.t :=
    snd (OpsRunner.solve Follows.program (Follows.facts two_links) ops_limits).

  (** Whether the database has the row of [follows] for two characters. *)
  Definition leads (a b : ascii) : bool :=
    OpsRunner.holds Follows.follows_code [AsciiEncode.encode a; AsciiEncode.encode b]
      follows_result.

  (** The two links lead from a to c. *)
  Example links_lead_to_the_end :
    leads "a" "c" = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The links have a direction. *)
  Example links_have_a_direction :
    leads "c" "a" = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End CharacterTests.

(** * Pairs *)

Module PairTests.

  Local Open Scope Z_scope.

  (** The engine value of a point. *)
  Definition point (p : Z * Z) : positive := encode_pair ZEncode.encode ZEncode.encode p.

  (** Two tagged points. *)
  Definition two_points : list ((Z * Z) * positive) :=
    [((1, -2), 1%positive); ((0, 5), 2%positive)].

  (** The database after running [Mirrors] on the two points. *)
  Definition mirror_result : OpsDatabase.t :=
    snd (OpsRunner.solve Mirrors.program (Mirrors.facts two_points) ops_limits).

  (** A point and its mirror image have a row. *)
  Example point_has_its_mirror :
    OpsRunner.holds Mirrors.mirrored_code [point (1, -2); point (-2, 1)] mirror_result = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A point is not its own mirror image when its coordinates differ. *)
  Example point_is_not_its_mirror :
    OpsRunner.holds Mirrors.mirrored_code [point (1, -2); point (1, -2)] mirror_result = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

End PairTests.

(** * Options *)

Module OptionTests.

  Local Open Scope positive_scope.

  (** A table with the value -4 at the key 1 and no value at the key 2. *)
  Definition two_entries : list (positive * option Z) := [(1, Some (-4)%Z); (2, None)].

  (** The database after running [Entries] on the two entries. *)
  Definition entry_result : OpsDatabase.t :=
    snd (OpsRunner.solve Entries.program (Entries.facts two_entries) ops_limits).

  (** The key 1 holds its value. *)
  Example key_holds_its_value :
    OpsRunner.holds Entries.entry_code
      [1; encode_option ZEncode.encode (Some (-4)%Z)] entry_result = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The literal [None] of [missing_in] selects the key 2. *)
  Example literal_none_selects_its_key :
    OpsRunner.holds Entries.missing_code [2] entry_result = true /\
    OpsRunner.holds Entries.missing_code [1] entry_result = false.
  Proof.
    vm_compute. split; reflexivity.
  Qed.

  (** The key without a value defaults to zero. *)
  Example missing_value_defaults_to_zero :
    OpsRunner.holds Entries.defaulted_code [2; ZEncode.encode 0%Z] entry_result = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End OptionTests.

(** * Lists of values *)

Module ListValueTests.

  Local Open Scope positive_scope.

  (** The engine value of a list of jobs. *)
  Definition jobs_value (ds : list positive) : positive := encode_list id_encode ds.

  (** The job 1 waits for nothing, and the job 2 waits for the jobs 1 and 3. *)
  Definition two_jobs : list job := [Job 1 []; Job 2 [1; 3]].

  (** The database after running [Jobs] on the two jobs. *)
  Definition jobs_result : OpsDatabase.t :=
    snd (OpsRunner.solve Jobs.program (Jobs.facts two_jobs) ops_limits).

  (** An input constructor puts its list into one value of its row. *)
  Example list_is_one_value_of_the_row :
    Jobs.facts [Job 2 [1; 3]] = [(Jobs.Job_code, [2; jobs_value [1; 3]])].
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The relation [waits] holds the list of a job. *)
  Example job_waits_for_its_list :
    OpsRunner.holds Jobs.waits_code [2; jobs_value [1; 3]] jobs_result = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The literal [[]] of [idle_job] selects the job without dependencies. *)
  Example empty_list_selects_the_idle_job :
    OpsRunner.holds Jobs.idle_code [1] jobs_result = true /\
    OpsRunner.holds Jobs.idle_code [2] jobs_result = false.
  Proof.
    vm_compute. split; reflexivity.
  Qed.

  (** The primitive [waits_for] finds the job 1 in the list of the job 2. *)
  Example job_is_blocked_by_its_dependency :
    OpsRunner.holds Jobs.blocked_code [2; 1] jobs_result = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** The job 3 is in the list of the job 2, but no input lists the job 3, so no row says that
      it blocks the job 2. *)
  Example unlisted_job_blocks_nothing :
    OpsRunner.holds Jobs.blocked_code [2; 3] jobs_result = false.
  Proof.
    vm_compute. reflexivity.
  Qed.

  (** A primitive on lists computes the reverse list. *)
  Example primitive_reverses_the_list :
    OpsRunner.holds Jobs.backwards_code [2; jobs_value [3; 1]] jobs_result = true.
  Proof.
    vm_compute. reflexivity.
  Qed.

End ListValueTests.

(** * Glue *)

Module GlueTests.

  (** An instance of [counted] gives the derived row of its encoded natural numbers. *)
  Example counted_gives_derived_row :
    derived Ops.prim Counts.spec (Counts.inputs [(0, 2)]%nat) Counts.counted_code
      [NatEncode.encode 0; NatEncode.encode 2].
  Proof.
    apply (proj1 (Counts.counted_spec [(0, 2)]%nat 0 2)).
    apply (counted_step [(0, 2)]%nat 0 2 2); [left; reflexivity | reflexivity].
  Qed.

  (** A derived row of encoded natural numbers gives the instance of [counted]. *)
  Example derived_row_gives_counted :
    derived Ops.prim Counts.spec (Counts.inputs [(0, 2)]%nat) Counts.counted_code
      [NatEncode.encode 0; NatEncode.encode 2] -> counted [(0, 2)]%nat 0 2.
  Proof.
    intros Hrow.
    exact (proj2 (Counts.counted_spec [(0, 2)]%nat 0 2) Hrow).
  Qed.

  (** An instance of [follows] gives the derived row of its encoded characters. *)
  Example follows_gives_derived_row :
    derived (fun _ _ => None) Follows.spec (Follows.inputs [("a", "b")]%char)
      Follows.follows_code [AsciiEncode.encode "a"%char; AsciiEncode.encode "b"%char].
  Proof.
    apply (proj1 (Follows.follows_spec _ [("a", "b")]%char "a"%char "b"%char)).
    apply follows_link. left. reflexivity.
  Qed.

  (** A derived row of encoded characters gives the instance of [follows]. *)
  Example derived_row_gives_follows :
    derived (fun _ _ => None) Follows.spec (Follows.inputs [("a", "b")]%char)
      Follows.follows_code [AsciiEncode.encode "a"%char; AsciiEncode.encode "b"%char] ->
    follows [("a", "b")]%char "a"%char "b"%char.
  Proof.
    intros Hrow.
    exact (proj2 (Follows.follows_spec _ [("a", "b")]%char "a"%char "b"%char) Hrow).
  Qed.

  (** The tagged point of the glue tests. *)
  Definition one_point : list ((Z * Z) * positive) := [((1, 2)%Z, 1%positive)].

  (** An instance of [mirrored] gives the derived row of its encoded pairs. *)
  Example mirrored_gives_derived_row :
    derived Ops.prim Mirrors.spec (Mirrors.inputs one_point) Mirrors.mirrored_code
      [PairTests.point (1, 2)%Z; PairTests.point (2, 1)%Z].
  Proof.
    apply (proj1 (Mirrors.mirrored_spec one_point (1, 2)%Z (2, 1)%Z)).
    apply (mirrored_point one_point (1, 2)%Z 1%positive (2, 1)%Z);
      [left; reflexivity | reflexivity].
  Qed.

  (** A derived row of encoded pairs gives the instance of [mirrored]. *)
  Example derived_row_gives_mirrored :
    derived Ops.prim Mirrors.spec (Mirrors.inputs one_point) Mirrors.mirrored_code
      [PairTests.point (1, 2)%Z; PairTests.point (2, 1)%Z] -> mirrored one_point (1, 2)%Z (2, 1)%Z.
  Proof.
    intros Hrow.
    exact (proj2 (Mirrors.mirrored_spec one_point (1, 2)%Z (2, 1)%Z) Hrow).
  Qed.

  (** The table of the glue tests, with no value at the key 2. *)
  Definition no_value : list (positive * option Z) := [(2%positive, None)].

  (** An instance of [defaulted] gives the derived row of its key and its integer. *)
  Example defaulted_gives_derived_row :
    derived Ops.prim Entries.spec (Entries.inputs no_value) Entries.defaulted_code
      [2%positive; ZEncode.encode 0%Z].
  Proof.
    apply (proj1 (Entries.defaulted_spec no_value 2%positive 0%Z)).
    apply (defaulted_entry no_value 2%positive None 0%Z); [| reflexivity].
    apply entry_in. left. reflexivity.
  Qed.

  (** A derived row of an option gives the instance of [entry]. *)
  Example derived_row_gives_entry :
    derived Ops.prim Entries.spec (Entries.inputs no_value) Entries.entry_code
      [2%positive; encode_option ZEncode.encode None] -> entry no_value 2%positive None.
  Proof.
    intros Hrow.
    exact (proj2 (Entries.entry_spec no_value 2%positive None) Hrow).
  Qed.

  (** The jobs of the glue tests. *)
  Definition one_job : list job := [Job 2%positive [1%positive]].

  (** An instance of [waits] gives the derived row of its encoded list. *)
  Example waits_gives_derived_row :
    derived Ops.prim Jobs.spec (Jobs.inputs one_job) Jobs.waits_code
      [2%positive; ListValueTests.jobs_value [1%positive]].
  Proof.
    apply (proj1 (Jobs.waits_spec one_job 2%positive [1%positive])).
    apply waits_job. left. reflexivity.
  Qed.

  (** A derived row of a list gives the instance of [backwards]. *)
  Example derived_row_gives_backwards :
    derived Ops.prim Jobs.spec (Jobs.inputs one_job) Jobs.backwards_code
      [2%positive; ListValueTests.jobs_value [1%positive]] ->
    backwards one_job 2%positive [1%positive].
  Proof.
    intros Hrow.
    exact (proj2 (Jobs.backwards_spec one_job 2%positive [1%positive]) Hrow).
  Qed.

End GlueTests.

(** * Rejections *)

Module RejectionTests.

  (** [present table k x] says that the entry at [k] holds the integer [x]. *)
  Inductive present (table : list (positive * option Z)) : positive -> Z -> Prop :=
    | present_in k x : In (k, Some x) table -> present table k x.

  (** A pattern writes a variable inside an option, which the engine holds as one value. *)
  Fail Egglog Present from present.

  (** The type of [rev] depends on its first argument, so [rev] has no encoders. *)
  Fail Egglog Primitives Polymorphic rev.

End RejectionTests.
