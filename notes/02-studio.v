(* Top level code is the "Vernacular" language *)
Require Import Frap.

Inductive bool : Set :=
| true
| false.

(* Galina programming language, pure and total *)
Definition notb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

(* cbv == call by value *)
Eval cbv in (notb true).
Eval cbv in (notb false).

(*args b1, b2 of type bool, return bool*)
Definition andb (b1 b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Lemma andb_comms :
  forall b1 b2,
    andb b1 b2 = andb b2 b1.
(*
Ltac is the proof scripting language, generating Galina code
  specifically, generates a value with the type == Lemma, to prove the Lemma

This is based on the Curry-Howard Isomorphism
*)
Proof.
  intros.
  cases b1; cases b2; auto.
Qed.

(*Inspect type*)
Check andb.

Inductive nat : Set :=
| O : nat
| S : nat -> nat.

Definition isZero (n : nat) : bool :=
  match n with
  | O => true
  | S _ => false
  end.

Lemma isZero_O :
  isZero O = true.
Proof.
  auto.
Qed.

Lemma isZero_O' :
  forall n,
  isZero n = true -> n = O.
Proof.
  intros.
  cases n.
  - reflexivity.
  - simpl in H. (* runs simple on hypothesis, not goal *)
    congruence.
Qed.

(*Definition add (n1 n2 : nat) : nat :=*)
Fixpoint add (n1 n2 : nat) : nat :=
  match n1 with
  | O => n2
  | S m1 => S (add m1 n2)
  end.

Eval cbv in (add O O).

Eval cbv in (add (S O) (S O)).

Lemma add_O_n :
  forall n,
    (*add n O = n. -- not so simple! the case below matches directly above *)
    add O n = n.
Proof.
  auto.
Qed.

(* This example shows how casing doesn't get us as far in natural numbers
   as it did for something finite like boolean

Lemma add_n_O :
  forall n,
    (*add n O = n. -- not so simple! the case below matches directly above *)
    add n O = n.
Proof.
  intros. (* introduce n variable *)
  cases n. (* split into subgoals based on inductive definition *)
  auto. (* 0 0 easy case *)
  simpl. (* basicaly applies the add function in the S case *)
  f_equal. (* transforms [ f (x1) = f (x2) ] -> [ x1 = x2 ] *)
  (* fuck! back to where we started! *)
Qed.
*)

Lemma add_n_O :
  forall n,
    (*add n O = n. -- not so simple! the case below matches directly above *)
    add n O = n.
Proof.
  intros. (* introduce n variable *)
  induct n.
  - auto.
  - rename n into m.
    simpl.
    (* method 1 *)
    rewrite IHn. (* apply IHn and replace in subgoal *)
    reflexivity. (* obvi S m = S m *)

    (* method 2
    f_equal. (* transforms [ f (x1) = f (x2) ] -> [ x1 = x2 ] *)
    assumption. (* use the assumption (IH) *)
    *)
Qed.

(* fp in coq *)
Inductive list (A : Set) : Set :=
| nil : list A
| cons : A -> list A -> list A.

Set Implicit Arguments.
Arguments nil {A}.
Arguments cons {A}.

Fixpoint length (A : Set) (l : list A) : nat :=
  match l with
  | nil => O (* nil takes a type argument! *)
  | cons _ m => S (length m)
  end.

Eval cbv in (length (cons true (cons false (cons true (nil))))).

Fixpoint map (A B : Set) (f : A -> B) (l : list A) : list B :=
  match l with
  | nil => nil
  | cons x xs => cons (f x) (map f xs)
  end.

Eval cbv in (map isZero (cons O (cons (S O) (cons (S (S O)) nil)))).

Fixpoint foldr (A B : Set) (f : A -> B -> B) (l : list A) (b : B) : B :=
  match l with
  | nil => b
  | cons x xs => f x (foldr f xs b)
      (* note foldr is not tail recursive *)
      (* tail recursion can affect proof difficulty! *)
  end.

(* adds                     0        + 1            + 2        + 0 *)
Eval cbv in (foldr add (cons O (cons (S O) (cons (S (S O)) nil))) O).

Lemma foldr_cons_id :
  forall A (l : list A),
    foldr (@cons A) l nil = l.
Proof.
  induct l; simpl; auto.
  rewrite IHl. auto.
Qed.
