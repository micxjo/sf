Require Export Utils Basics.

Theorem andb_true_elim1 : forall b c : bool,
                            andb b c = true -> b = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
    reflexivity.
  Case "b = false".
    rewrite <- H.
    reflexivity.
Qed.

Theorem andb_true_elim2 : forall b c : bool,
                            andb b c = true -> c = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
    simpl in H.
    rewrite -> H.
    reflexivity.
  Case "b = false".
    destruct c.
    SCase "c = true".
      reflexivity.
    SCase "c = false".
      simpl in H.
      rewrite -> H.
      reflexivity.
Qed.

Theorem plus_O_r : forall n : nat, n + 0 = n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0". reflexivity.
  Case "n = S h'". simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem minus_diag : forall n : nat,
                       minus n n = 0.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0". simpl. reflexivity.
  Case "n = S n'". simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem mult_O_r : forall n : nat,
                     n * 0 = 0.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0". reflexivity.
  Case "n = S n'". simpl. rewrite -> IHn'. reflexivity.
Qed.