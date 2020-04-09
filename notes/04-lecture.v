Require Import Frap.

Lemma add_comm :
  forall a b,
    a + b = b + a.
Proof.
Show Proof.
  induct a.
Show Proof.
Print nat_ind.
  + simplify.
Show Proof. (* Notice simplify doesn't actually "do" anything to the proof term *)

(* TIP 1: Try to avoid nested induction *)
(* Instead: try searching through all the theorems to find something of a certain shape *)
Search (_ = _ + 0).  (* this found a plus_n_0 theorem *)
  apply plus_n_O.
Show Proof.
  + simplify.
Show Proof.
  rewrite IHa. (* plug relevant vars into Inductive Hypothesis *)
Show Proof.
(* The current goal "S (b + a) = b + S a" would require induction on second arg *)
(* Instead try search again *)
Search (_ + S _ = S (_ + _)).  (* and find Nat.add_succ_r *)
  symmetry.
Show Proof.
  apply Nat.add_succ_r.
Show Proof. (* Now there are no ?Goals, and we're done *)
Qed.

(*  TIP 2: Use "debug auto." to see what "auto." is doing !  *)
