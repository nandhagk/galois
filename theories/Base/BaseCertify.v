(** * Certification

    A sound boolean checker can attach a proof to an accepted candidate.
    For example, a checker for even numbers can certify an even candidate.
    Builds on: Rocq Stdlib booleans and dependent pairs. *)

From Stdlib Require Import Bool.

(** Check a candidate and attach the proof supplied by the soundness theorem. *)
Definition certify {W : Type} (P : W -> Prop) (check : W -> bool)
    (sound : forall w, check w = true -> P w) (w : W) : option {w : W | P w} :=
  match Bool.bool_dec (check w) true with
  | left H => Some (exist P w (sound w H))
  | right _ => None
  end.

(** Certification exposes its boolean decision and retains the original candidate. *)
Theorem certify_equation {W : Type} (P : W -> Prop) (check : W -> bool)
    (sound : forall w, check w = true -> P w) (w : W) :
  certify P check sound w =
    match Bool.bool_dec (check w) true with
    | left H => Some (exist P w (sound w H))
    | right _ => None
    end.
Proof.
  reflexivity.
Qed.

(** Return a certified fallback when the checker rejects the candidate. *)
Definition certify_or {W : Type} (P : W -> Prop) (check : W -> bool)
    (sound : forall w, check w = true -> P w) (fallback : {w : W | P w})
    (w : W) : {w : W | P w} :=
  match certify P check sound w with
  | Some result => result
  | None => fallback
  end.

(** Certification succeeds exactly when the checker accepts the candidate. *)
Theorem certify_some_iff {W : Type} (P : W -> Prop) (check : W -> bool)
    (sound : forall w, check w = true -> P w) (w : W) :
  (exists result, certify P check sound w = Some result) <-> check w = true.
Proof.
  unfold certify.
  destruct (Bool.bool_dec (check w) true) as [Hcheck | Hcheck].
  - split.
    + intros _. exact Hcheck.
    + intros _. eexists. reflexivity.
  - split.
    + intros [result Hresult]. discriminate Hresult.
    + intros H. contradiction.
Qed.

(** The candidate or fallback returned by certification satisfies the property. *)
Theorem certify_or_sound {W : Type} (P : W -> Prop) (check : W -> bool)
    (sound : forall w, check w = true -> P w) (fallback : {w : W | P w})
    (w : W) : P (proj1_sig (certify_or P check sound fallback w)).
Proof.
  exact (proj2_sig (certify_or P check sound fallback w)).
Qed.
