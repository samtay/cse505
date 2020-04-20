Inductive bool : Set :=
| true
| false.

Definition notb (b : bool) : bool :=
  match b with
  | true => false
  | false => true
  end.

Definition andb (b1 b2 : bool) : bool :=
  match b1 with
  | true => b2
  | false => false
  end.

Lemma andb_comm :
  forall b1 b2,
    andb b1 b2 = andb b2 b1.
Proof.
  intro b1.
  intro b2.
  destruct b1.
    - destruct b2.
      + reflexivity.
      + simpl. reflexivity.
    - destruct b2.
      + simpl. reflexivity.
      + reflexivity.
Qed.

Print andb_comm.