(* Transition systems *)
Require Import Frap.

Set Implicit Arguments.

Fixpoint fact (n : nat) : nat :=
  match n with
  | O => 1
  | S n' => fact n' * S n'
  end.
Inductive fact_state :=
| AnswerIs (answer : nat)
| WithAccumulator (input accumulator : nat).

Inductive fact_init (original_input : nat) : fact_state -> Prop :=
| FactInit : fact_init original_input (WithAccumulator original_input 1).

Check fact_init. (* fact_init : nat -> fact_state -> Prop *)
(* so fact_init is a type constructor that takes a natural number, a
*  fact_state, and produces a type whose type is Prop *)

(* Notice the args to a type constructor before the initial colon
*  (original_input above) are automatically arguments to each of
*  the inductive constructors *)

Check (fact_init 2 (AnswerIs 5)).
(* Produces a type whose type is Prop. Happens to be false! *)

Lemma fool :
  fact_init 3 (WithAccumulator 3 1).
Proof.
  Show Proof.
  exact (FactInit 3).
  Restart.
  constructor. (* or find the right constructor automatically *)
  Show Proof.
Qed.

Lemma foo2 :
  not (fact_init 5 (WithAccumulator 3 1)).
Proof.
  Print not.
  unfold not.
  intros.
  invert H. (* find the only way we could have made H, via FactInit *)
Qed.

(*
*  thought: why doesn't Coq just restrict type system so that we can only construct
*           fact_inits via the FactInit constructor?
*
*  ben: we want a language that's strong enough to encode false statements
*)

Inductive fact_final : fact_state -> Prop :=
| FactFinal : forall ans, fact_final (AnswerIs ans).

Inductive fact_step : fact_state -> fact_state -> Prop :=
| FactDone : forall acc,
  fact_step (WithAccumulator O acc) (AnswerIs acc)
| FactStep : forall n acc,
  fact_step (WithAccumulator (S n) acc) (WithAccumulator n (acc * S n)).

Inductive trc {A} (R : A -> A -> Prop) : A -> A -> Prop :=
| TrcRefl : forall x, trc R x x
| TrcFront : forall x y z,
  R x y
  -> trc R y z
  -> trc R x z.

Set Warnings "-notation-overridden".
Notation "R ^*" := (trc R) (at level 0).

(* Now let's use it to execute the factorial program. *)
Example factorial_3 : fact_step^* (WithAccumulator 3 1) (AnswerIs 6).
Proof.
  try constructor. (* fails with "unable to find instance for variable y" *)
  econstructor. (* pretend y exists for a minute *)
  constructor.
  econstructor.
  constructor.
  econstructor.
  constructor.
  econstructor.
  constructor.
  simplify.
  constructor. (* TrcRefl *)
Qed.
