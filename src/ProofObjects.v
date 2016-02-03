Require Export MoreLogic.

Theorem six_is_beautiful: beautiful 6.
Proof.
  apply b_sum with (n:=3) (m:=3).
  apply b_3.
  apply b_3.
Qed.

Definition six_is_beautiful': beautiful 6 :=
  b_sum 3 3 b_3 b_3.

Theorem nine_is_beautiful: beautiful 9.
Proof.
  apply b_sum with (n:=3) (m:=6).
  apply b_3.
  apply six_is_beautiful.
Qed.

Definition nine_is_beautiful': beautiful 9 :=
  b_sum 3 6 b_3 six_is_beautiful.

Theorem b_plus3: forall n, beautiful n -> beautiful (3+n).
Proof.
  intros n H.
  apply b_sum.
  apply b_3.
  apply H.
Qed.

Definition b_plus3': forall n, beautiful n -> beautiful (3+n) :=
  fun (n:nat) => fun (H:beautiful n) =>
                   b_sum 3 n b_3 H.

Definition b_plus3'' (n:nat) (H:beautiful n) : beautiful (3+n) :=
  b_sum 3 n b_3 H.

Definition b_times2' : forall n, beautiful n -> beautiful (2*n) :=
  fun (n:nat) => fun (H:beautiful n) =>
                   b_sum n (n + 0) H (b_sum n 0 H b_0).

Definition gorgeous_plus13_po : forall n, gorgeous n -> gorgeous (13 + n) :=
  fun (n:nat) => fun (H:gorgeous n) =>
                   g_plus3 (10 + n)
                           (g_plus5 (5 + n)
                                    (g_plus5 n H)).

Definition conj_fact : forall P Q R, P /\ Q  -> Q /\ R -> P /\ R :=
  fun (P Q R : Prop) (H1: P /\ Q) =>
    fun (H2: Q /\ R) =>
      match H1 with
        | conj HP HQ =>
          match H2 with
            | conj HQ HR => conj P R HP HR
          end
      end.

Definition beautiful_iff_gorgeous : forall n, beautiful n <-> gorgeous n :=
  fun (n:nat) =>
    conj (beautiful n -> gorgeous n)
         (gorgeous n -> beautiful n)
         (beautiful__gorgeous n)
         (gorgeous__beautiful n).

Definition or_commut'' : forall P Q, P \/ Q -> Q \/ P :=
  fun (P Q : Prop) =>
    fun (HPQ : P \/ Q) =>
      match HPQ with
        | or_introl HP => or_intror Q P HP
        | or_intror HQ => or_introl Q P HQ
      end.

Lemma plus_comm_r : forall a b c, c + (b + a) = c + (a + b).
Proof.
  intros a b c.
  rewrite (plus_comm b a).
  reflexivity.
Qed.

Lemma plus_comm_r' : forall a b c, c + (b + a) = c + (a + b).
Proof.
  intros a b c.
  rewrite (plus_comm b).
  reflexivity.
Qed.

Lemma plus_comm_r'' : forall a b c, c + (b + a) = c + (a + b).
Proof.
  intros a b c.
  rewrite (plus_comm _ a).
  reflexivity.
Qed.

Lemma plus_comm_r''' : forall a b c, c + (b + a) = c + (a + b).
Proof.
  intros a b c.
  rewrite plus_comm with (n := b).
  reflexivity.
Qed.

Example trans_eq_example' : forall (a b c d e f : nat),
                              [a;b] = [c;d] ->
                              [c;d] = [e;f] ->
                              [a;b] = [e;f].
Proof.
  intros a b c d e f H1 H2.
  apply (trans_eq _ _ [c;d]).
  apply H1.
  apply H2.
Qed.
