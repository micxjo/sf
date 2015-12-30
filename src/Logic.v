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
