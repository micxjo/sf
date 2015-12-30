Require Export MoreCoq.

Inductive and (P Q : Prop) : Prop :=
  conj : P -> Q -> (and P Q).

Notation "P /\ Q" := (and P Q) : type_scope.

Theorem and_example :
  (0 = 0) /\ (4 = mult 2 2).
Proof.
  apply conj.
  Case "left". reflexivity.
  Case "right". reflexivity.
Qed.

Theorem and_example' :
  (0 = 0) /\ (4 = mult 2 2).
Proof.
  split.
  Case "left". reflexivity.
  Case "right". reflexivity.
Qed.

Theorem proj1: forall (P Q : Prop),
                 P /\ Q -> P.
Proof.
  intros P Q H.
  destruct H as [HP HQ].
  apply HP.
Qed.

Theorem proj2 : forall (P Q : Prop),
                  P /\ Q -> Q.
Proof.
  intros P Q H.
  destruct H as [HP HQ].
  apply HQ.
Qed.

Theorem and_commut : forall (P Q : Prop),
                       P /\ Q -> Q /\ P.
Proof.
  intros P Q H.
  destruct H as [HP HQ].
  split.
  Case "left". apply HQ.
  Case "right". apply HP.
Qed.

Theorem and_assoc : forall (P Q R : Prop),
                      P /\ (Q /\ R) -> (P /\ Q) /\ R.
Proof.
  intros P Q R H.
  destruct H as [HP [HQ HR]].
  split.
  split.
  apply HP.
  apply HQ.
  apply HR.
Qed.

Definition iff (P Q : Prop) := (P -> Q) /\ (Q -> P).

Notation "P <-> Q" := (iff P Q)
                        (at level 95, no associativity)
                      : type_scope.

Theorem iff_implies : forall (P Q : Prop),
                        (P <-> Q) -> P -> Q.
Proof.
  intros P Q H.
  destruct H as [HAB HBA].
  apply HAB.
Qed.

Theorem iff_sym : forall (P Q : Prop),
                    (P <-> Q) -> (Q <-> P).
Proof.
  intros P Q H.
  destruct H as [HAB HBA].
  split.
  Case "->". apply HBA.
  Case "<-". apply HAB.
Qed.

Theorem iff_refl : forall (P : Prop),
                     P <-> P.
Proof.
  intros P; split; intros HP; apply HP.
Qed.

Theorem iff_trans : forall (P Q R : Prop),
                      (P <-> Q) -> (Q <-> R) -> (P <-> R).
Proof.
  intros P Q R H0 H1.
  destruct H0 as [HPQ HQP].
  destruct H1 as [HQR HRQ].
  split.
  Case "P -> R".
    intros H.
    apply HPQ in H.
    apply HQR in H.
    apply H.
  Case "R -> P".
    intros H.
    apply HRQ in H.
    apply HQP in H.
    apply H.
Qed.

Inductive or (P Q : Prop) : Prop :=
| or_introl : P -> or P Q
| or_intror : Q -> or P Q.

Notation "P \/ Q" := (or P Q) : type_scope.

Theorem or_commut : forall P Q : Prop,
                      P \/ Q -> Q \/ P.
Proof.
  intros P Q H.
  destruct H as [HP | HQ].
  right.
  apply HP.
  left.
  apply HQ.
Qed.

Theorem or_distributes_over_and_1 : forall (P Q R : Prop),
                                      P \/ (Q /\ R) -> (P \/ Q) /\ (P \/ R).
Proof.
  intros P Q R H. destruct H as [HP | [HQ HR]].
  Case "left".
    split.
    SCase "left". left. apply HP.
    SCase "right". left. apply HP.
  Case "right".
    split.
    SCase "left". right. apply HQ.
    SCase "right". right. apply HR.
Qed.

Theorem or_distributes_over_and_2 :
  forall (P Q R : Prop),
    (P \/ Q) /\ (P \/ R) -> P \/ (Q /\ R).
Proof.
  intros P Q R H. destruct H as [H1 H2].
  destruct H1 as [HP | HQ].
  left. apply HP.
  destruct H2 as [HP | HR].
  left.
  apply HP.
  right.
  split.
  apply HQ.
  apply HR.
Qed.

Theorem andb_prop : forall b c,
                      andb b c = true -> b = true /\ c = true.
Proof.
  intros b c H.
  destruct b.
  Case "b = true".
    destruct c.
    SCase "c = true". apply conj. reflexivity. reflexivity.
    SCase "c = false". inversion H.
  Case "b = false". inversion H.
Qed.

Theorem andb_true_intro : forall b c,
                            b = true /\ c = true -> andb b c = true.
Proof.
  intros b c H.
  destruct H.
  rewrite H.
  rewrite H0.
  reflexivity.
Qed.

Theorem andb_false : forall b c,
                       andb b c = false -> b = false \/ c = false.
Proof.
  intros b c H.
  destruct b.
  simpl in H.
  right.
  apply H.
  simpl in H.
  left.
  apply H.
Qed.

Theorem orb_prop : forall b c,
                     orb b c = true -> b = true \/ c = true.
Proof.
  intros b c H.
  destruct b.
  simpl in H.
  left.
  apply H.
  simpl in H.
  right.
  apply H.
Qed.

Theorem orb_false_elim : forall b c,
                           orb b c = false -> b = false /\ c = false.
Proof.
  intros b c H.
  destruct b.
  inversion H.
  split.
  reflexivity.
  destruct c.
  inversion H.
  reflexivity.
Qed.

Inductive False : Prop := .

Theorem False_implies_nonsense :
  False -> 2 + 2 = 5.
Proof.
  intros contra.
  inversion contra.
Qed.

Theorem nonsense_implies_False :
  2 + 2 = 5 -> False.
Proof.
  intros contra.
  inversion contra.
Qed.

Theorem ex_falso_quodlibet : forall (P:Prop),
                               False -> P.
Proof.
  intros p contra.
  inversion contra.
Qed.

Inductive True : Prop :=
  tt : True.

Definition not (P:Prop) := P -> False.

Notation "~ x" := (not x) : type_scope.

Theorem not_False :
  ~ False.
Proof.
  unfold not. intros H.
  inversion H.
Qed.

Theorem contradiction_implies_anything : forall (P Q : Prop),
                                           (P /\ ~P) -> Q.
Proof.
  intros P Q H. destruct H as [HP HNA].
  unfold not in HNA.
  apply HNA in HP.
  inversion HP.
Qed.

Theorem double_neg : forall P : Prop,
                       P -> ~~P.
Proof.
  intros P H.
  unfold not.
  intros G.
  apply G.
  apply H.
Qed.

Theorem contrapositive : forall (P Q : Prop),
                           (P -> Q) -> (~Q -> ~P).
Proof.
  intros P Q H HnQ.
  unfold not.
  intros HP.
  apply H in HP.
  apply contradiction_implies_anything with (P:=Q).
  split.
  apply HP.
  apply HnQ.
Qed.

Theorem not_both_true_and_false : forall (P:Prop),
                                    ~(P /\ ~P).
Proof.
  intros P.
  unfold not.
  intros H.
  apply contradiction_implies_anything with (P:=P).
  apply H.
Qed.

Theorem excluded_middle_irrefutable : forall (P:Prop),
                                        ~~(P \/ ~P).
Proof.
  intros P.
  unfold not.
  intros H.
  apply H.
  right.
  intros H1.
  apply H.
  left.
  apply H1.
Qed.

Notation "x <> y" := (~ (x = y)) : type_scope.

Theorem not_false_then_true : forall b : bool,
                                b <> false -> b = true.
Proof.
  intros b H. destruct b.
  Case "b = true". reflexivity.
  Case "b = false".
    unfold not in H.
    apply ex_falso_quodlibet.
    apply H.
    reflexivity.
Qed.

Theorem false_beq_nat : forall (n m : nat),
                          n <> m ->
                          beq_nat n m = false.
Proof.
  intros n. induction n as [|n'].
  Case "n = 0".
    intros m H.
    destruct m as [|m'].
    SCase "m = 0".
      simpl.
      apply ex_falso_quodlibet.
      apply H.
      reflexivity.
      SCase "m = S m'". reflexivity.
  Case "n = S n'".
    intros m H.
    destruct m as [|m'].
    SCase "m = 0". reflexivity.
    SCase "m = S m'".
    simpl.
    apply IHn'.
    unfold not.
    intros Hnm.
    unfold not in H.
    apply H.
    apply f_equal.
    apply Hnm.
Qed.

Theorem beq_nat_false : forall (n m : nat),
                          beq_nat n m = false -> n <> m.
Proof.
  intros n. induction n as [|n'].
  Case "n = 0".
    intros m H.
    destruct m as [|m'].
    SCase "m = 0".
      unfold not.
      intros H0.
      inversion H.
    SCase "m = S m'".
      unfold not.
      intros H0Sm.
      inversion H0Sm.
  Case "n = S n'".
    intros m H.
    destruct m as [|m'].
    SCase "m = 0".
      unfold not.
      intros HSn0.
      inversion HSn0.
    SCase "m = S m'".
      unfold not.
      intros HSnSm.
      simpl in H.
      apply IHn' in H.
      unfold not in H.
      inversion HSnSm.
      apply H in H1.
      apply H1.
Qed.
