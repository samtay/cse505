(********************** Begin: FRAP Preamble **********************)
Require Import Frap.

Inductive arith : Set :=
| Const (n : nat)
| Var (x : var)
| Plus (e1 e2 : arith)
| Minus (e1 e2 : arith)
| Times (e1 e2 : arith).

Example ex1 := Const 42.
Example ex2 := Plus (Var "y") (Times (Var "x") (Const 3)).

Definition valuation := fmap var nat.

Fixpoint interp (e : arith) (v : valuation) : nat :=
  match e with
  | Const n => n
  | Var x =>
    match v $? x with
    | None => 0
    | Some n => n
    end
  | Plus e1 e2 => interp e1 v + interp e2 v
  | Minus e1 e2 => interp e1 v - interp e2 v
  | Times e1 e2 => interp e1 v * interp e2 v
  end.

Definition valuation0 : valuation :=
  $0 $+ ("x", 17) $+ ("y", 3).

Theorem interp_ex1 : interp ex1 valuation0 = 42.
Proof.
  simplify.
  equality.
Qed.

Theorem interp_ex2 : interp ex2 valuation0 = 54.
Proof.
  unfold valuation0.
  simplify.
  equality.
Qed.

Fixpoint commuter (e : arith) : arith :=
  match e with
  | Const _ => e
  | Var _ => e
  | Plus e1 e2 => Plus (commuter e2) (commuter e1)
  | Minus e1 e2 => Minus (commuter e1) (commuter e2)
  | Times e1 e2 => Times (commuter e2) (commuter e1)
  end.
(********************** End: FRAP Preamble **********************)

(********************** Begin: Studio talk **********************)
Theorem commuter_ok : forall v e, interp (commuter e) v = interp e v.
Proof.
  intros.
  induct e; simplify.
  - equality.
  - equality.
  - linear_arithmetic.
  - equality.
  - rewrite IHe1, IHe2.
    remember (interp e2 v) as a.
    remember (interp e1 v) as b.
    (* ring.              [> ring knows a*b = b*a <] *)
    (* Show Proof.        [> 259 line proof <] *)
    linear_arithmetic. (* why does linear_arithmetic work here? :shrug: *)
    (* Show Proof.        [> 333 line proof <] *)
    Locate linear_arithmetic.
Qed.
(* Ring is just a decision procedure; as long as your datatype has proven its
*  axioms, you can use proofs about rings for free. *)

(* Note: linear_arithmetic is not equivalent to ring *)
(* Recall: ring can only prove equalities, l_a can prove both equalities and
*  inequalities. *)
(********************** End: Studio Talk **********************)

(********************** Begin: my solution **********************)
Fixpoint doSomeArithmetic (e : arith) : arith :=
  match e with
  | Const _ => e
  | Var _ => e
  | Plus (Const n1) (Const n2) => Const (n1 + n2)
  | Plus e1 e2 => Plus (doSomeArithmetic e1) (doSomeArithmetic e2)
  | Minus e1 e2 => Minus (doSomeArithmetic e1) (doSomeArithmetic e2)
  | Times (Const n1) (Const n2) => Const (n1 * n2)
  | Times e1 e2 => Times (doSomeArithmetic e1) (doSomeArithmetic e2)
  end.

(* Just case bashin' *)
Theorem doSomeArithmetic_ok : forall e v, interp (doSomeArithmetic e) v = interp e v.
Proof.
  induct e; simplify.
  - equality.
  - equality.
  - cases e1; simplify; try equality.
    cases e2; simplify; equality.
  - cases e1; simplify; equality.
  - cases e1; simplify; try equality.
    cases e2; simplify; equality.
Qed.
(********************** End: my solution **********************)

(********************** Begin: FRAP Stuff **********************)
Inductive instruction :=
| PushConst (n : nat)
| PushVar (x : var)
| Add
| Subtract
| Multiply.

Definition run1 (i : instruction) (v : valuation) (stack : list nat) : list nat :=
  match i with
  | PushConst n => n :: stack
  | PushVar x => (match v $? x with
                  | None => 0
                  | Some n => n
                  end) :: stack
  | Add =>
    match stack with
    | arg2 :: arg1 :: stack' => arg1 + arg2 :: stack'
    | _ => stack
    end
  | Subtract =>
    match stack with
    | arg2 :: arg1 :: stack' => arg1 - arg2 :: stack'
    | _ => stack
    end
  | Multiply =>
    match stack with
    | arg2 :: arg1 :: stack' => arg1 * arg2 :: stack'
    | _ => stack
    end
  end.

Fixpoint run (is : list instruction) (v : valuation) (stack : list nat) : list nat :=
  match is with
  | nil => stack
  | i :: is' => run is' v (run1 i v stack)
  end.

Fixpoint compile (e : arith) : list instruction :=
  match e with
  | Const n => PushConst n :: nil
  | Var x => PushVar x :: nil
  | Plus e1 e2 => compile e1 ++ compile e2 ++ Add :: nil
  | Minus e1 e2 => compile e1 ++ compile e2 ++ Subtract :: nil
  | Times e1 e2 => compile e1 ++ compile e2 ++ Multiply :: nil
  end.
(********************** End: FRAP Stuff **********************)

(********************** Begin: Studio Talk **********************)
Theorem compile_ok' : forall e v, run (compile e) v nil = interp e v :: nil.
Proof.
  induct e; intros; simplify; auto.
  - try rewrite IHe1. (* this hypothesis is not syntactically equivalent to the current goal
                         in particular, it only hypothesizes running a single compilation
                         we NEED a stronger induction hypothesis! hence compile_ok_stronger *)
Admitted.

(* so lets do this for all instruction lists, not just single compiles *)
Theorem compile_ok_stronger :
  forall e v is,
    run (compile e ++ is) v nil = run is v (interp e v :: nil).
Proof.
  induct e; intros; simplify; auto.
  - try rewrite IHe1. (* still doesn't work, BUT just a silly nesting reason. *)
    Search ((_ ++ _) ++ _ = _ ++ (_ ++ _)). (* so let's find what we need *)
    rewrite app_assoc_reverse.
    rewrite IHe1. (* great! *)
    rewrite app_assoc_reverse.
    try rewrite IHe2.
    (* BUT this doesn't work for the second side! the IH works
       for empty instruction stacks but what we need to prove is no longer
       empty! there's an `interp e1 v` sitting in there. So this theorem statement
       is NOT inductive. *)
Admitted.

(* so lets make sure we have a statement for ALL stacks, not just nil *)
Theorem compile_ok_even_stronger :
  forall e v is stack,
    run (compile e ++ is) v stack = run is v (interp e v :: stack).
Proof.
  induct e; intros; simplify; auto.
  - rewrite <- app_assoc. (* same thing as rewrite app_assoc_reverse. *)
    rewrite IHe1.
    rewrite <- app_assoc.
    rewrite IHe2. (* Notice IHe2 is now strong enough for the goal! *)
    simplify. reflexivity.
  (* the other cases are identical *)
  - rewrite <- app_assoc. rewrite IHe1.
    rewrite <- app_assoc. rewrite IHe2. simplify. reflexivity.
  - rewrite <- app_assoc. rewrite IHe1.
    rewrite <- app_assoc. rewrite IHe2. simplify. reflexivity.
Qed.

(* Finding the right inductive hypothesis is an art. It needs to be weak enough
   to prove base cases but strong enough to induct. *)

Theorem compile_ok : forall e v, run (compile e) v nil = interp e v :: nil.
Proof.
  intros.
  try apply compile_ok_even_stronger. (* doesn't work directly *)
  SearchRewrite (_ ++ nil).
  rewrite (app_nil_end (compile e)). (* pass (compile e ++ []) instead of (compile e) *)
  apply compile_ok_even_stronger.
Qed.

(********************** End: Studio Talk **********************)
