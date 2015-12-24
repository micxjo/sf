Require Export Poly.

Theorem silly_ex :
  (forall n, evenb n = true -> oddb (S n) = true) ->
  evenb 3 = true ->
  oddb 4 = true.
Proof.
  intros eq1 eq2.
  apply eq1.
  apply eq2.
Qed.

Theorem rev_exercise1 : forall (l l' : list nat),
                          l = rev l' ->
                          l' = rev l.
Proof.
  intros l l' H.
  rewrite -> H.
  symmetry.
  apply rev_involutive.
Qed.

Theorem trans_eq : forall (X:Type) (n m o : X),
                     n = m -> m = o -> n = o.
Proof.
  intros X n m o eq1 eq2.
  rewrite -> eq1.
  rewrite -> eq2.
  reflexivity.
Qed.

Example trans_eq_example : forall (a b c d e f : nat),
                             [a;b] = [c;d] ->
                             [c;d] = [e;f] ->
                             [a;b] = [e;f].
Proof.
  intros a b c d e f eq1 eq2.
  apply trans_eq with (m:=[c;d]).
  apply eq1.
  apply eq2.
Qed.

Example trans_eq_exercise : forall (n m o p : nat),
                              m = (minustwo o) ->
                              (n + p) = m ->
                              (n + p) = (minustwo o).
Proof.
  intros n m o p eq1 eq2.
  apply trans_eq with (m:=m).
  apply eq2.
  apply eq1.
Qed.

Theorem eq_add_S : forall (n m : nat),
                     S n = S m ->
                     n = m.
Proof.
  intros n m eq. inversion eq. reflexivity.
Qed.

Example sillyex1 : forall (X:Type) (x y z : X) (l j : list X),
                     x :: y :: l = z :: j ->
                     y :: l = x :: j ->
                     x = y.
Proof.
  intros X x y z l j H1 H2.
  inversion H2.
  reflexivity.
Qed.

Example sillyex2 : forall (X:Type) (x y z : X) (l j : list X),
                     x :: y :: l = [] ->
                     y :: l = z :: j ->
                     x = z.
Proof.
  intros X x y z l j H1 H2.
  inversion H1.
Qed.

Theorem f_equal : forall (A B : Type) (f:A->B) (x y : A),
                    x = y -> f x = f y.
Proof.
  intros A B f x y H.
  rewrite H.
  reflexivity.
Qed.

Theorem beq_nat_0_l : forall n,
                        beq_nat 0 n = true -> n = 0.
Proof.
  intros n H. destruct n as [|n'].
  Case "n = 0". reflexivity.
  Case "n = S n'". inversion H.
Qed.

Theorem beq_nat_0_r : forall n,
                        beq_nat n 0 = true -> n = 0.
Proof.
  intros n H. destruct n as [|n'].
  Case "n = 0". reflexivity.
  Case "n = S n'". inversion H.
Qed.

Theorem S_inj : forall (n m : nat) (b:bool),
                  beq_nat (S n) (S m) = b ->
                  beq_nat n m = b.
Proof.
  intros n m b H.
  simpl in H.
  apply H.
Qed.

Theorem silly3' : forall (n:nat),
                    (beq_nat n 5 = true -> beq_nat (S (S n)) 7 = true) ->
                    true = beq_nat n 5 ->
                    true = beq_nat (S (S n)) 7.
Proof.
  intros n eq H.
  symmetry in H.
  apply eq in H.
  symmetry in H.
  apply H.
Qed.

Theorem plus_n_n_injective : forall n m,
                               n + n = m + m ->
                               n = m.
Proof.
  intros n. induction n as [|n'].
  Case "n = 0".
    intros m H.
    destruct m as [|m'].
    SCase "m = 0". reflexivity.
    SCase "m = S m'". inversion H.
  Case "n = S n'".
    intros m H.
    destruct m as [|m'].
    SCase "m = 0". inversion H.
    SCase "m = S m'".
      simpl in H.
      repeat rewrite <- plus_n_Sm in H.
      inversion H.
      apply IHn' in H1.
      rewrite H1.
      reflexivity.
Qed.
