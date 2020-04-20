(* Debug methods:

- idtac : to print at the tactic level

- debug auto : print everything auto does

*)
Theorem very_true : forall x : Set, x = x.
Proof.
  idtac "print me alone".
  idtac "concat this";
  idtac "with this".
  debug auto.
Qed.

(* Functions and quantifiers:

- Every function (a -> b) is actually syntactic sugar for
  (forall a:t, b)

- If the snd of the tuple is not bound by the quantifier,
  then we can treat this as a function a -> b.

- All function types are expressed with "forall".

- But function types are written with arrows only when the result
  *type* does not depend on the *value* of the argument.
*)
Check (forall n: nat, bool). (* nat -> bool : Set *)

(* Dependent types:

-  Simply: types that depend on values.
|> Theorem wow: forall e v, interp (arithemtic e) v = interp e v
    - the type of 'wow' depends on the values e, v.
*)
Check 3. (* nat *)
Check nat. (* Set *)
Check Set. (* Type *)
Check Type. (* Type *)

(* Type is actually an infinite hierarchy:

- We need this for type soundness

If we enable "display universe levels" in Coq, we see
that Type@{type 1}'s type is actually Type@{type 1+1}.

Prop is parallel to Set in the type hierarchy, because we want to keep theorem
types from program types. (There are many reasons why a program should not be
dependent on proofs about itself.)
*)
Check (forall m n, m < n). (* Prop *)
Check Prop. (* Type@{Set+1} *)
