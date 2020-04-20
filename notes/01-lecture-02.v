Require Import Frap.

(* The following definition closely mirrors a standard BNF grammar for expressions.
 * It defines abstract syntax trees of arithmetic expressions. *)
Inductive arith : Set :=
| Const (n : nat)
| Plus (e1 e2 : arith)
| Times (e1 e2 : arith).

(* Here are a few examples of specific expressions. *)
Example ex1 := Const 42.
Example ex2 := Plus (Const 1) (Times (Const 2) (Const 3)).

(* How many nodes appear in the tree for an expression? *)
Fixpoint size (e : arith) : nat :=
  match e with
  | Const _ => 1
  | Plus e1 e2 => 1 + size e1 + size e2
  | Times e1 e2 => 1 + size e1 + size e2
  end.

(* Here's how to run a program (evaluate a term) in Coq. *)
Compute size ex1.
Compute size ex2.

(* These are two different ASTs! evaluated equality !== true equality *)
Lemma weird :
  Plus (Const 1) (Const 1) = Const 2 ->
  False.
Proof.
  congruence.
Qed.

(* False is a type with no constructors, so we cant actually build values of
   type False! *)
Print False.
Inductive MyFalse : Prop := .

Lemma myfalse_false:
  MyFalse <-> False.
Proof.
  split; intros.
  - destruct H.
  - contradiction.
Qed.

(* This is also an empty type, we can't actually build values with this
   constructor *)
Inductive yo : Prop :=
| Yo : yo -> yo.

Lemma yoyo:
  yo -> False.
Proof.
  intros.
  destruct H. (* not helping! *)
  destruct H. (* not helping! *)
  induct H.
  contradiction.
Qed.

(* We also have True which, contrastly, is immediately producable! *)
Print True.
(*
Inductive True : Prop :=  I : True
*)
