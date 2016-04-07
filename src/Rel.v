Require Export SfLib.

Definition partial_function {X:Type} (R: relation X) :=
  forall x y1 y2 : X, R x y1 -> R x y2 -> y1 = y2.

Theorem next_nat_partial_function :
  partial_function next_nat.
Proof.
  unfold partial_function.
  intros x y1 y2 H1 H2.
  inversion H1.
  inversion H2.
  reflexivity.
Qed.

Theorem le_not_a_partial_function :
  ~ (partial_function le).
Proof.
  unfold not. unfold partial_function. intros Hc.
  assert (0 = 1) as Nonsense.
  Case "Proof of assertion".
    apply Hc with (x := 0).
    apply le_n.
    apply le_S.
    apply le_n.
  inversion Nonsense.
Qed.

Theorem total_relation_not_partial_function :
  ~ (partial_function total_relation).
Proof.
  unfold not. unfold partial_function. intros Hc.
  assert (O = S O) as Nonsense.
  apply Hc with O.
  apply tot.
  apply tot.
  inversion Nonsense.
Qed.
  
Theorem empty_relation_partial_function :
  partial_function empty_relation.
Proof.
  unfold partial_function.
  intros x y1 y2 H1 H2.
  inversion H1.
Qed.

Definition reflexive {X:Type} (R: relation X) :=
  forall a : X, R a a.

Theorem le_reflexive :
  reflexive le.
Proof.
  unfold reflexive. intros n. apply le_n.
Qed.

Definition transitive {X:Type} (R: relation X) :=
  forall a b c : X, (R a b) -> (R b c) -> (R a c).

Theorem le_trans :
  transitive le.
Proof.
  intros n m o Hnm Hmo.
  induction Hmo.
  Case "le_n". apply Hnm.
  Case "le_S". apply le_S. apply IHHmo.
Qed.

Theorem lt_trans :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  apply le_S in Hnm.
  apply le_trans with (a := (S n)) (b := (S m)) (c := o).
  apply Hnm.
  apply Hmo.
Qed.

Theorem lt_trans' :
  transitive lt.
Proof.
  unfold lt. unfold transitive.
  intros n m o Hnm Hmo.
  induction Hmo as [| m' Hm'o].
  apply le_S.
  apply Hnm.
  apply le_S.
  apply IHHm'o.
Qed.

Theorem le_Sn_le : forall n m, S n <= m -> n <= m.
Proof.
  intros n m H. apply le_trans with (S n).
  apply le_S.
  apply le_n.
  apply H.
Qed.

Theorem le_S_n : forall n m,
                   (S n <= S m) -> (n <= m).
Proof.
  intros n m H.
  inversion H.
  apply le_n.
  apply le_Sn_le in H1.
  apply H1.
Qed.

Theorem le_Sn_n : forall n,
                    ~ (S n <= n).
Proof.
  induction n.
  intros H.
  inversion H.
  unfold not in IHn.
  intros H.
  apply le_S_n in H.
  apply IHn.
  apply H.
Qed.
