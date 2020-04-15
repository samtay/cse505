(*** Defining Either ***)

(*
A B are parameterized
  - automatically passed to each constructor
  - each constructor must return `either A B`
*)
Inductive either (A B : Set) : Set :=
| left : A -> either A B
| right : B -> either A B.

(* this needs to come AFTER left/right definition *)
Set Implicit Arguments.
Arguments left {A B}.
Arguments right {A B}.

Check either.
Check (either nat bool).
Check (left).


Definition getRight (A B : Set) (e : either A B) : option B :=
  match e with
  | left _ => None
  | right b => Some b
  end.

Eval cbv in getRight (left 0).
Eval cbv in getRight (right 1).

