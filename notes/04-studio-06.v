Set Warnings "-notation-overridden".

Require Import Frap TransitionSystems.

Set Implicit Arguments.

(* invariant1 is a subset of invariant2 *)
Definition oneStepClosure_current {state} (sys : trsys state)
           (invariant1 invariant2 : state -> Prop) :=
  forall st, invariant1 st
             -> invariant2 st.

(* step(invariant1) is a subset of invariant2 *)
Definition oneStepClosure_new {state} (sys : trsys state)
           (invariant1 invariant2 : state -> Prop) :=
  forall st st', invariant1 st
                 -> sys.(Step) st st'
                 -> invariant2 st'.

Definition oneStepClosure {state} (sys : trsys state)
           (invariant1 invariant2 : state -> Prop) :=
  oneStepClosure_current sys invariant1 invariant2
  /\ oneStepClosure_new sys invariant1 invariant2.

Theorem prove_oneStepClosure : forall state (sys : trsys state) (inv1 inv2 : state -> Prop),
  (forall st, inv1 st -> inv2 st)
  -> (forall st st', inv1 st -> sys.(Step) st st' -> inv2 st')
  -> oneStepClosure sys inv1 inv2.
Proof.
  unfold oneStepClosure.
  propositional.
Qed.

Theorem oneStepClosure_done : forall state (sys : trsys state) (invariant : state -> Prop),
  (forall st, sys.(Initial) st -> invariant st)
  (* if something is invariant for all initial states *)
  -> oneStepClosure sys invariant invariant
  (* and invariant is closed under any one step *)
  -> invariantFor sys invariant.
  (* then it is an invariant for the whole system *)
Proof.
  unfold oneStepClosure, oneStepClosure_current, oneStepClosure_new.
  propositional.
  apply invariant_induction.
  assumption.
  simplify.
  eapply H2.
  eassumption.
  assumption.
Qed.

(* compare to transitive reflexive closure *)
Inductive multiStepClosure {state} (sys : trsys state)
  : (state -> Prop) -> (state -> Prop) -> Prop :=

(* if one-step closure has no effect, we're done *) (* ~ nil *)
| MscDone : forall inv,
    oneStepClosure sys inv inv
    -> multiStepClosure sys inv inv

(* otherwise we need to recurse *) (* ~ cons *)
| MscStep : forall inv inv' inv'',
    oneStepClosure sys inv inv'
    -> multiStepClosure sys inv' inv''
    -> multiStepClosure sys inv inv''.

Lemma multiStepClosure_ok' : forall state (sys : trsys state) (inv inv' : state -> Prop),
  multiStepClosure sys inv inv'
  -> (forall st, sys.(Initial) st -> inv st)
  -> invariantFor sys inv'.
Proof.
  induct 1; simplify.

  apply oneStepClosure_done.
  assumption.
  assumption.

  apply IHmultiStepClosure.
  simplify.
  unfold oneStepClosure, oneStepClosure_current in *.
  (* TODO is this * just all available hypotheses? *)
  propositional.
  apply H3.
  apply H1.
  assumption.
Qed.

Theorem multiStepClosure_ok : forall state (sys : trsys state) (inv : state -> Prop),
  multiStepClosure sys sys.(Initial) inv
  -> invariantFor sys inv.
Proof.
  simplify.
  eapply multiStepClosure_ok'.
  eassumption.
  propositional.
Qed.

Theorem oneStepClosure_empty : forall state (sys : trsys state),
  oneStepClosure sys (constant nil) (constant nil).
Proof.
  unfold oneStepClosure, oneStepClosure_current, oneStepClosure_new; propositional.
Qed.

Theorem oneStepClosure_split : forall state (sys : trsys state) st sts (inv1 inv2 : state -> Prop),
  (forall st', sys.(Step) st st' -> inv1 st')
  -> oneStepClosure sys (constant sts) inv2
  -> oneStepClosure sys (constant (st :: sts)) ({st} \cup inv1 \cup inv2).
Proof.
  unfold oneStepClosure, oneStepClosure_current, oneStepClosure_new; propositional.

  invert H0.

  left. (* to prove A or B, switch to proving A *)
  left.
  simplify.
  propositional.

  right.
  apply H1.
  assumption.

  simplify.
  propositional.

  right.
  left.
  apply H.
  equality.

  right.
  right.
  eapply H2.
  eassumption.
  assumption.
Qed.

Theorem singleton_in : forall {A} (x : A) rest,
  ({x} \cup rest) x.
Proof.
  simplify.
  left.
  simplify.
  equality.
Qed.

Definition fact_correct (original_input : nat) (st : fact_state) : Prop :=
  match st with
  | AnswerIs ans => fact original_input = ans
  | WithAccumulator _ _ => True
    (* ^ this time around, we don't care about intermediate states *)
    (* (include all of them in our invariant) *)
  end.

Theorem fact_init_is : forall original_input,
  fact_init original_input = {WithAccumulator original_input 1}.
Proof.
  simplify.
  apply sets_equal; simplify.
  propositional.

  invert H.
  equality.

  rewrite <- H0.
  constructor.
Qed.

(* we can crunch this down by enumerating all states *)
Theorem factorial_ok_2 :
  invariantFor (factorial_sys 2) (fact_correct 2).
Proof.
  eapply invariant_weaken.

  apply multiStepClosure_ok.
  simplify.
  rewrite fact_init_is.

  eapply MscStep.
  apply oneStepClosure_split.
  simplify.
  invert H.
  apply singleton_in.
  apply oneStepClosure_empty.
  simplify.

  eapply MscStep.
  apply oneStepClosure_split.
  simplify.
  invert H.
  apply singleton_in.
  apply oneStepClosure_split.
  simplify.
  invert H.
  apply singleton_in.
  apply oneStepClosure_empty.
  simplify.

  eapply MscStep.
  apply oneStepClosure_split.
  simplify.
  invert H.
  apply singleton_in.
  apply oneStepClosure_split.
  simplify.
  invert H.
  apply singleton_in.
  apply oneStepClosure_split.
  simplify.
  invert H.
  apply singleton_in.
  apply oneStepClosure_empty.
  simplify.

  apply MscDone.
  apply prove_oneStepClosure; simplify.
  assumption.
  propositional; subst; invert H0; simplify; propositional.

  simplify.
  unfold fact_correct.
  propositional; subst; trivial.
Qed.

Hint Rewrite fact_init_is.

(* instead of doing all that by hand, write a tactic that will do it for us! *)
Ltac model_check_done :=
  apply MscDone; apply prove_oneStepClosure; simplify; propositional; subst;
  repeat match goal with
         | [ H : _ |- _ ] => invert H
         end; simplify; equality.

Theorem singleton_in_other : forall {A} (x : A) (s1 s2 : set A),
  s2 x
  -> (s1 \cup s2) x.
Proof.
  simplify.
  right.
  right.
  assumption.
Qed.

Ltac singletoner :=
  repeat match goal with
         | _ => apply singleton_in
         | [ |- (_ \cup _) _ ] => apply singleton_in_other
         end.

Ltac model_check_step0 :=
  eapply MscStep; [
    repeat ((apply oneStepClosure_empty; simplify)
            || (apply oneStepClosure_split; [ simplify;
                                              repeat match goal with
                                                     | [ H : _ |- _ ] => invert H; try congruence
                                                     end; solve [ singletoner ] | ]))
  | simplify ].

Ltac model_check_step :=
  match goal with
  | [ |- multiStepClosure _ ?inv1 _ ] =>
    model_check_step0;
    match goal with
    | [ |- multiStepClosure _ ?inv2 _ ] =>
      (assert (inv1 = inv2) by compare_sets; fail 3)
      || idtac
    end
  end.

Ltac model_check_steps1 := model_check_step || model_check_done.
Ltac model_check_steps := repeat model_check_steps1.

Ltac model_check_finish := simplify; propositional; subst; simplify; equality.

Ltac model_check_infer :=
  apply multiStepClosure_ok; simplify; model_check_steps.

Ltac model_check_find_invariant :=
  simplify; eapply invariant_weaken; [ model_check_infer | ]; cbv beta in *.

Ltac model_check := model_check_find_invariant; model_check_finish.

Theorem factorial_ok_2_snazzy :
  invariantFor (factorial_sys 2) (fact_correct 2).
Proof.
  model_check.
Qed.

Theorem factorial_ok_3 :
  invariantFor (factorial_sys 3) (fact_correct 3).
Proof.
  model_check.
Qed.

Theorem factorial_ok_5 :
  invariantFor (factorial_sys 5) (fact_correct 5).
Proof.
  model_check.
Qed.

(* notice it takes some time to find the invariant! *)
Theorem factorial_ok_5_again :
  invariantFor (factorial_sys 5) (fact_correct 5).
Proof.
  model_check_find_invariant.
  model_check_finish.
Qed.


Inductive isEven : nat -> Prop :=
| EvenO : isEven 0
| EvenSS : forall n, isEven n -> isEven (S (S n)).

Inductive add2_thread :=
| Read
| Write (local : nat).

Inductive add2_init : threaded_state nat add2_thread -> Prop :=
| Add2Init : add2_init {| Shared := 0; Private := Read |}.

Inductive add2_step : threaded_state nat add2_thread -> threaded_state nat add2_thread -> Prop :=
| StepRead : forall global,
    add2_step {| Shared := global; Private := Read |}
              {| Shared := global; Private := Write global |}
| StepWrite : forall global local,
    add2_step {| Shared := global; Private := Write local |}
              {| Shared := S (S local); Private := Read |}.

Definition add2_sys1 := {|
  Initial := add2_init;
  Step := add2_step
|}.

Definition add2_sys := parallel add2_sys1 add2_sys1.

Definition add2_correct (st : threaded_state nat (add2_thread * add2_thread)) :=
  isEven st.(Shared).

Inductive simulates state1 state2 (R : state1 -> state2 -> Prop)
  (sys1 : trsys state1) (sys2 : trsys state2) : Prop :=
| Simulates :
  (forall st1, sys1.(Initial) st1
               -> exists st2, R st1 st2
                              /\ sys2.(Initial) st2)

  -> (forall st1 st2, R st1 st2
                      -> forall st1', sys1.(Step) st1 st1'
                                      -> exists st2', R st1' st2'
                                                      /\ sys2.(Step) st2 st2')

  -> simulates R sys1 sys2.

Inductive invariantViaSimulation state1 state2 (R : state1 -> state2 -> Prop)
  (inv2 : state2 -> Prop)
  : state1 -> Prop :=
| InvariantViaSimulation : forall st1 st2, R st1 st2
  -> inv2 st2
  -> invariantViaSimulation R inv2 st1.

Lemma invariant_simulates' : forall state1 state2 (R : state1 -> state2 -> Prop)
  (sys1 : trsys state1) (sys2 : trsys state2),
  (forall st1 st2, R st1 st2
                   -> forall st1', sys1.(Step) st1 st1'
                                   ->  exists st2', R st1' st2'
                                                    /\ sys2.(Step) st2 st2')
  -> forall st1 st1', sys1.(Step)^* st1 st1'
                      -> forall st2, R st1 st2
                                     -> exists st2', R st1' st2'
                                                     /\ sys2.(Step)^* st2 st2'.
Proof.
  induct 2.

  simplify.
  exists st2.
  propositional.
  constructor.

  simplify.
  eapply H in H2.
  first_order.
  apply IHtrc in H2.
  first_order.
  exists x1.
  propositional.
  econstructor.
  eassumption.
  assumption.
  assumption.
Qed.
