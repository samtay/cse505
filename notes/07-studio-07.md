# lambda calculus in coq

We can demonstrate that the lambda calculus is Turing-complete in Coq:

```coq
(* Some notations, to let us write more normal-looking lambda terms *)
Coercion Var : var >-> exp.
Notation "\ x , e" := (Abs x e) (at level 50).
Infix "@" := App (at level 49, left associativity).

Example omega := (\"x", "x" @ "x") @ (\"x", "x" @ "x").

Theorem omega_no_eval : forall v, eval omega v -> False.
Proof.
  induct 1.
  (* Invert eval hypotheses *)
  invert H.
  invert H0.
  simplify.
  apply IHeval3.
  trivial.
Qed.
```
That is, Omega doesn't terminate.

Here's a formal definition of the Z combinator mentioned in last lecture
```coq
Definition Z :=
  \"f", (\"x", "f" @ (\"v", "x" @ "x" @ "v"))
      @ (\"x", "f" @ (\"v", "x" @ "x" @ "v")).
```
