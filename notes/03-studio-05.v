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

(* Compare fact_step ... *)

Inductive fact_step : fact_state -> fact_state -> Prop :=
| FactDone : forall acc,
  fact_step (WithAccumulator O acc) (AnswerIs acc)
| FactStep : forall n acc,
  fact_step (WithAccumulator (S n) acc) (WithAccumulator n (acc * S n)).

(* to a more typical definition ... *)

Definition plus : nat -> nat -> nat :=
  (* the actual defn *)
  fun a => fun b => a + b.

(*
Notice fact_step doesn't read as directly. It's a type that takes two values
and produces a type whose type is Prop.

But the only way to construct _values_ that inhibit the type `fact_step s1 s2`
are via the `FactDone` and `FactStep` constructors.

Also, fact_step, FactDone, FactStep are fundamentally different than plus. When
we apply values to the former constructors, we don't compute and return values.
Essentially all that happens when we apply values to the former is that we tag
certain values to have certain types.
*)

Inductive trc {A} (R : A -> A -> Prop) : A -> A -> Prop :=
| TrcRefl : forall x, trc R x x
| TrcFront : forall x y z,
  R x y
  -> trc R y z
  -> trc R x z.
Set Warnings "-notation-overridden".
Notation "R ^*" := (trc R) (at level 0).

(* See 06-lecture.v for where we proved this initially *)
Example factorial_3 : fact_step^* (WithAccumulator 3 1) (AnswerIs 6).
Proof.
  (* repeat can be used to continue trying something until it stops making progress *)

  (* repeat (let x := fresh in assert (x : True) by auto). makes infinite loop! *)

  repeat (econstructor).
Qed.

Record trsys state := {
  Initial : state -> Prop;
  Step : state -> state -> Prop
}.

Definition factorial_sys (original_input : nat) : trsys fact_state := {|
  Initial := fact_init original_input;
  Step := fact_step
|}.

(* the {type} curly braces mean the type can be implicit and inferred by type
*  checker.
*
*  to pass in {type} manually, prefix the function by '@'.
*)

Inductive reachable {state} (sys : trsys state) (st : state) : Prop :=
| Reachable : forall st0,
  sys.(Initial) st0
  -> sys.(Step)^* st0 st
  -> reachable sys st.
(*
Even though we use `forall`, we read as `exists`.
*)
Print ex.
(*
Inductive ex (A : Type) (P : A -> Prop) : Prop :=
    ex_intro : forall x : A, P x -> exists y, P y

So to build a _value_ of this type, we pass in _any_ x to ex_intro,
such that P x is true.

This is just because this is how constructors work, they take _any_ values that
their type implies. By also requiring P x, the ability to call ex_intro (P x),
we have shown that such an x does exist!
*)

Lemma foo :
  exists n, n = S O.
Proof.
  exists 1; auto.
Qed.

Definition invariantFor {state} (sys : trsys state) (invariant : state -> Prop) :=
  forall s, sys.(Initial) s
            -> forall s', sys.(Step)^* s s'
                          -> invariant s'.

(* for example, trivially, reachability is an invariant ! *)
Lemma bar :
  forall {state} (sys: trsys state),
    invariantFor sys (reachable sys).
Proof.
  intros.
  unfold invariantFor.
  intros.
  (* Notice H and H0 are precisely the arguments of the Reachable constructor
     to create the `reachable sys s'` goal!  *)
  econstructor; eauto.
Qed.

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
  (* induct 2 inducts on the second inductively defined datatype in the statement,
     in this case:  sys.(Step)^* s s'
   *)
  induct 2; propositional.
  apply IHtrc.
  eapply H; eauto.
  (* Many times this well let Coq find the right arg to H.
     If it doesn't work, we can manually specify, but it might have been better
     to just use apply (H x) in the first place. *)
Qed.
