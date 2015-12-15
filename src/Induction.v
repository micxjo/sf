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

Theorem plus_n_Sm : forall n m : nat,
                      S (n + m) = n + (S m).
Proof.
  intros n m. induction n as [| n'].
  Case "n = 0". reflexivity.
  Case "n = S n'". simpl. rewrite -> IHn'. reflexivity.
Qed.

Theorem plus_comm : forall n m : nat,
                      n + m = m + n.
Proof.
  intros n m. induction n as [| n'].
  Case "n = 0". simpl. rewrite <- plus_n_O. reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'. rewrite -> plus_n_Sm.
    reflexivity.
Qed.

Theorem plus_assoc : forall n m p : nat,
                       n + (m + p) = (n + m) + p.
Proof.
  intros n m p. induction n as [| n'].
  Case "n = 0". simpl. reflexivity.
  Case "n = S n'". simpl. rewrite -> IHn'. reflexivity.
Qed.

Fixpoint double (n:nat) :=
  match n with
    | O => O
    | S n' => S (S (double n'))
  end.

Lemma double_plus : forall n, double n = n + n.
Proof.
  intros n. induction n as [| n'].
  Case "n = O". reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'. rewrite -> plus_n_Sm.
    reflexivity.
Qed.

Theorem mult_O_plus' : forall n m : nat,
                         (0 + n) * m = n * m.
Proof.
  intros n m.
  assert (H: O + n = n).
    Case "Proof of assertion". reflexivity.
  rewrite -> H.
  reflexivity.
Qed.

Theorem plus_rearrange : forall n m p q : nat,
                           (n + m) + (p + q) = (m + n) + (p + q).
Proof.
  intros n m p q.
  assert (H: n + m = m + n).
    Case "Proof of assertion".
    rewrite -> plus_comm. reflexivity.
  rewrite -> H. reflexivity.
Qed.

Theorem plus_swap : forall n m p : nat,
                      n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  assert (H: n + m = m + n). rewrite -> plus_comm. reflexivity.
  rewrite -> H. rewrite -> plus_assoc.
  reflexivity.
Qed.

Theorem mult_plus : forall m n : nat,
                      n * S m = n + n * m.
Proof.
  intros m n. induction n as [| n'].
  Case "n = 0". reflexivity.
  Case "n = S n'".
  simpl.
  rewrite -> IHn'. rewrite -> plus_swap.
  reflexivity.
Qed.

Theorem mult_comm : forall m n : nat,
                      m * n = n * m.
Proof.
  intros m n. induction n as [| n'].
  Case "n = 0". rewrite -> mult_O_r. reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> mult_plus. rewrite -> IHn'.
    reflexivity.
Qed.

Theorem evenb_n__oddb_Sn : forall n : nat,
                             evenb n = negb (evenb (S n)).
Proof.
  intros n. induction n as [| n'].
  Case "n = 0". reflexivity.
  Case "n = S n'".
    assert (H: evenb (S (S n')) = evenb n'). reflexivity.
    rewrite -> H. rewrite -> IHn'. rewrite -> negb_involutive.
    reflexivity.
Qed.

Theorem ble_nat_refl : forall n : nat,
                         true = ble_nat n n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0". reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem zero_nbeq_S : forall n : nat,
                        beq_nat 0 (S n) = false.
Proof.
  intros n. reflexivity.
Qed.

Theorem andb_false_r : forall b : bool,
                         andb b false = false.
Proof.
  intros b. destruct b; reflexivity.
Qed.

Lemma plus_O_l : forall n : nat,
                   0 + n = n.
Proof.
  reflexivity.
Qed.

Theorem plus_ble_compat_l :
  forall n m p : nat,
    ble_nat n m = true -> ble_nat (p + n) (p + m) = true.
Proof.
  intros n m p H. induction p as [| p']; simpl.
  Case "p = 0". rewrite -> H. reflexivity.
  Case "p = S p'". rewrite -> IHp'. reflexivity.
Qed.

Theorem S_nbeq_O : forall n : nat,
                     beq_nat (S n) 0 = false.
Proof.
  intros n. reflexivity.
Qed.

Theorem mult_1_l : forall n : nat, 1 * n = n.
Proof.
  intros n. simpl. rewrite -> plus_O_r. reflexivity.
Qed.

Theorem all3_spec :
  forall b c : bool,
    orb
      (andb b c)
      (orb (negb b)
           (negb c))
    = true.
Proof.
  intros b c.
  destruct b; destruct c; reflexivity.
Qed.

Theorem mult_plus_distr_r : forall n m p : nat,
                              (n + m) * p = (n * p) + (m * p).
Proof.
  intros n m p. induction n as [| n'].
  Case "n = 0". reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'. rewrite -> plus_assoc.
    reflexivity.
Qed.

Theorem mult_assoc : forall n m p : nat,
                       n * (m * p) = (n * m) * p.
Proof.
  intros n m p. induction n as [| n'].
  Case "n = 0". reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'. rewrite -> mult_plus_distr_r.
    reflexivity.
Qed.

Theorem beq_nat_refl : forall n : nat,
                         true = beq_nat n n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0". reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> IHn'.
    reflexivity.
Qed.

Theorem plus_swap' : forall n m p : nat,
                       n + (m + p) = m + (n + p).
Proof.
  intros n m p.
  rewrite -> plus_assoc.
  replace (n + m) with (m + n).
  rewrite -> plus_assoc.
  reflexivity.

  Case "n + m = m + n".
  rewrite -> plus_comm.
  reflexivity.
Qed.

Theorem bin_to_nat_pres_incr :
  forall b : bin,
    bin_to_nat (bin_incr b) = (bin_to_nat b) + 1.
Proof.
  intros b. induction b as [| b'| b''].
  Case "b = Z". reflexivity.
  Case "b = Twice b'". reflexivity.
  Case "b = STwice b''".
    simpl.
    rewrite -> IHb''.
    repeat rewrite -> plus_O_r.
    rewrite -> plus_swap.
    repeat rewrite -> plus_assoc.
    reflexivity.
Qed.

Fixpoint nat_to_bin (n:nat) : bin :=
  match n with
    | O => Z
    | S n' => bin_incr (nat_to_bin n')
  end.

Theorem nat_to_bin_to_nat :
  forall n : nat, bin_to_nat (nat_to_bin n) = n.
Proof.
  intros n. induction n as [| n'].
  Case "n = 0". reflexivity.
  Case "n = S n'".
    simpl.
    rewrite -> bin_to_nat_pres_incr.
    rewrite -> IHn'.
    rewrite -> plus_comm.
    reflexivity.
Qed.

Fixpoint normalize (b:bin) : bin :=
  match b with
    | Z => Z
    | Twice b' => nat_to_bin (bin_to_nat b)
    | STwice b' => nat_to_bin (bin_to_nat b)
  end.

Theorem bin_to_nat_to_bin :
  forall b : bin, nat_to_bin (bin_to_nat b) = normalize b.
Proof.
  intros b. destruct b as [| b'| b'']; reflexivity.
Qed.
