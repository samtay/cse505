(*

If you have programs that don't terminate,

an _interpreter_ will not be able to prove all of its semantics.

Instead, we can use _transisition systems_.

*)

(********************** Begin: FRAP Preamble **********************)
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

Example factorial_3 : fact_step^* (WithAccumulator 3 1) (AnswerIs 6).
Proof.
Admitted.

Record trsys state := {
  Initial : state -> Prop;
  Step : state -> state -> Prop
}.

Definition factorial_sys (original_input : nat) : trsys fact_state := {|
  Initial := fact_init original_input;
  Step := fact_step
|}.

Inductive reachable {state} (sys : trsys state) (st : state) : Prop :=
| Reachable : forall st0,
  sys.(Initial) st0
  -> sys.(Step)^* st0 st
  -> reachable sys st.
(********************** End: FRAP Preamble **********************)

(*
Q: why is sys.(Initial) s necessary in `forall s, sys.(Initial) s` ?
A: look at its definition, this means `forall s that is an initial state of sys`
   so altogether, this is the statement:
   "forall initial states s of sys,
     forall states s' reachable from s,
      invariant holds for s'"
*)
Definition invariantFor {state} (sys : trsys state) (invariant : state -> Prop) :=
  forall s, sys.(Initial) s
            -> forall s', sys.(Step)^* s s'
                          -> invariant s'.

(********************** Begin: FRAP Preamble **********************)
Lemma use_invariant' : forall {state} (sys : trsys state)
  (invariant : state -> Prop) s s',
  invariantFor sys invariant
  -> sys.(Initial) s
  -> sys.(Step)^* s s'
  -> invariant s'.
Proof.
  unfold invariantFor.
  simplify.
  eapply H.
  eassumption.
  assumption.
Qed.

Theorem use_invariant : forall {state} (sys : trsys state)
  (invariant : state -> Prop) s,
  invariantFor sys invariant
  -> reachable sys s
  -> invariant s.
Proof.
  simplify.
  invert H0.
  eapply use_invariant'.
  eassumption.
  eassumption.
  assumption.
Qed.

Lemma invariant_induction' : forall {state} (sys : trsys state)
  (invariant : state -> Prop),
  (forall s, invariant s -> forall s', sys.(Step) s s' -> invariant s')
  -> forall s s', sys.(Step)^* s s'
     -> invariant s
     -> invariant s'.
Proof.
  induct 2; propositional.
  apply IHtrc.
  eapply H.
  eassumption.
  assumption.
Qed.

Theorem invariant_induction : forall {state} (sys : trsys state)
  (invariant : state -> Prop),
  (forall s, sys.(Initial) s -> invariant s)
  -> (forall s, invariant s -> forall s', sys.(Step) s s' -> invariant s')
  -> invariantFor sys invariant.
Proof.
  unfold invariantFor; intros.
  eapply invariant_induction'.
  eassumption.
  eassumption.
  apply H.
  assumption.
Qed.

Definition fact_invariant (original_input : nat) (st : fact_state) : Prop :=
  match st with
  | AnswerIs n => fact original_input = n
  | WithAccumulator n acc => fact original_input = acc * fact n
  end.
(********************** End: FRAP Preamble **********************)

(*
Invert is very similar to cases or destruct, but it is smarter
in that it can look backwards, looking at constraints in the type signature:

"s is Initial => s was made with fact_init => s looks like WithAccumulator"
*)
Theorem fact_invariant_ok : forall original_input,
  invariantFor (factorial_sys original_input) (fact_invariant original_input).
Proof.
  intros.
  apply invariant_induction; simplify.
  - invert H. simplify. auto.
  - invert H0; simplify; linear_arithmetic.
Qed.
