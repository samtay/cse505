(** * Compilation of arithmetic expressions to stack machine code *)

From Coq Require Import List String ZArith Extraction ExtrOcamlBasic.
Open Scope Z_scope.
Open Scope string_scope.
Open Scope list_scope.

(** ** The source language: arithmetic expressions. *)

(** Abstract syntax *)

Definition var: Type := string.

Inductive expr: Type :=
  | Const (n: Z)                (**r an integer constant *)
  | Var (v: var)                (**r a variable *)
  | Sum (e1: expr) (e2: expr)   (**r e1 + e2 *)
  | Diff (e1: expr) (e2: expr). (**r e1 - e2 *)

(** Denotational semantics: the meaning of an expression is the integer
    value it denotes.  This is just an evaluation function,
    parameterized by an environment associating values to variables. *)

Definition environment := var -> Z.

Fixpoint eval (env: environment) (e: expr) : Z :=
  match e with
  | Const n => n
  | Var v => env v
  | Sum e1 e2 => eval env e1 + eval env e2
  | Diff e1 e2 => eval env e1 - eval env e2
  end.

(** ** The target language: a stack machine in the style of HP calculators *)

(** Instruction set *)

Inductive instruction: Type :=
  | PushConst (n: Z)   (* push n *)
  | PushVar (v: var)   (* push value of variable v *)
  | Add                (* pop two integers, push their sum *)
  | Opp.               (* pop one integer, push its opposite *)

Definition code := list instruction.

(** Operational semantics *)

Definition stack := list Z.
Definition state := (code * environment * stack)%type.

(** Execution of the first instruction of the code sequence.
    Presented as a transition relation between
   "machine state before" and "machine state after". *)

Inductive step: state -> state -> Prop :=
  | step_pushconst: forall n c env stk,
      step (PushConst n :: c, env, stk)
           (c,                env, n :: stk)
  | step_pushvar: forall v c env stk,
      step (PushVar v :: c, env, stk)
           (c,              env, env v :: stk)
  | step_add: forall c env n1 n2 stk,
      step (Add :: c, env, n2 :: n1 :: stk)
           (c,        env, (n1 + n2) :: stk)
  | step_opp: forall c env n stk,
      step (Opp :: c, env, n :: stk)
           (c,        env, (-n):: stk).

(** Zero, one or several successive machine steps. *)

Inductive steps: state -> state -> Prop :=
  | steps_refl: forall s,
      steps s s
  | steps_one: forall s s',
      step s s' -> steps s s'
  | steps_trans: forall s1 s2 s3,
      steps s1 s2 -> steps s2 s3 ->
      steps s1 s3.

(** What it means for the machine to halt safely
    after having executed the given code [c]. *)

Definition machine_run (c: code) (env: environment) (result: Z) : Prop :=
  steps (c, env, nil) (nil, env, result :: nil).

(** ** Compilation *)

(** Compilation of arithmetic expressions to machine code.
    This is the familiar translation to "Reverse Polish Notation". *)

Fixpoint compile_expr (e: expr) : code :=
  match e with
  | Const n    => PushConst n :: nil
  | Var v      => PushVar v :: nil
  | Sum e1 e2  => compile_expr e1 ++ compile_expr e2 ++ Add :: nil
  | Diff e1 e2 => compile_expr e1 ++ compile_expr e2 ++ Opp :: Add :: nil
  end.

(** Such function definitions are executable, both within Coq... *)

Compute (compile_expr (Diff (Var "x") (Sum (Var "y") (Const 1)))).

(** ... and by generation of OCaml, Haskell or Scheme programs. *)

Recursive Extraction compile_expr.

(** This is the statement of correctness for our compiler. *)

Theorem compile_program_correct:
  forall e env,
  machine_run (compile_expr e) env (eval env e).
Proof.
Abort.

(** To prove it, we need to do an induction over the expression [e],
    and to strengthen the statement. *)

Lemma compile_expr_correct:
  forall e c env stk,
  steps (compile_expr e ++ c, env, stk)
        (c,                   env, eval env e :: stk).
Proof.
  induction e; intros; simpl.
- (** Case e = Const n *)
  apply steps_one. apply step_pushconst.
- (** Case e = Var v *)
  apply steps_one. apply step_pushvar.
- (** Case e = Sum e1 e2 *)
  rewrite !app_ass. simpl.
  eapply steps_trans. apply IHe1.
  eapply steps_trans. apply IHe2.
  apply steps_one. apply step_add.
- (** Case e = Diff e1 e2 *)
  rewrite !app_ass. simpl.
  eapply steps_trans. apply IHe1.
  eapply steps_trans. apply IHe2.
  eapply steps_trans. apply steps_one. apply step_opp.
  replace (eval env e1 - eval env e2)
     with (eval env e1 + - (eval env e2))
       by omega.
  apply steps_one. apply step_add.
Qed.

(** The original correctness statement is then a corollary. *)

Theorem compile_program_correct:
  forall e env,
  machine_run (compile_expr e) env (eval env e).
Proof.
  intros. red.
  replace (compile_expr e) with (compile_expr e ++ nil)
       by apply app_nil_r.
  apply compile_expr_correct.
Qed.

(** A more automated proof *)

Hint Constructors step steps.

Lemma compile_expr_correct':
  forall e c env stk,
  steps (compile_expr e ++ c, env, stk)
        (c,                   env, eval env e :: stk).
Proof.
  induction e; intros; simpl; rewrite ?app_ass; simpl; eauto.
- (** Case e = Diff e1 e2 *)
  replace (eval env e1 - eval env e2)
     with (eval env e1 + - (eval env e2))
       by omega.
  eauto 6.
Qed.

