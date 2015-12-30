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

Theorem double_injective : forall n m,
                             double n = double m ->
                             n = m.
Proof.
  intros n. induction n as [|n'].
  Case "n = 0".
    simpl.
    intros m H. destruct m as [|m'].
    SCase "m = 0". reflexivity.
    SCase "m = S m'". inversion H.
  Case "n = S n'".
    intros m H.
    destruct m as [|m'].
    SCase "m = 0". inversion H.
    SCase "m = S m'".
      apply f_equal.
      apply IHn'.
      inversion H.
      reflexivity.
Qed.

Theorem beq_nat_true : forall n m,
                         beq_nat n m = true -> n = m.
Proof.
  intros n. induction n as [|n'].
  Case "n = 0".
    intros m H. destruct m as [|m'].
    SCase "m = 0". reflexivity.
    SCase "m = S m'". inversion H.
  Case "n = S n'".
    intros m H. destruct m as [|m'].
    SCase "m = 0". inversion H.
    SCase "m = S m'".
      inversion H.
      apply IHn' in H1.
      apply f_equal.
      inversion H1.
      reflexivity.
Qed.

Theorem double_injective_take2 : forall n m,
                                   double n = double m ->
                                   n = m.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [|m'].
  Case "m = 0".
    simpl.
    intros n H. destruct n as [|n'].
    SCase "n = 0". reflexivity.
    SCase "n = S n'". inversion H.
  Case "m = S m'".
    intros n H. destruct n as [|n'].
    SCase "n = 0". inversion H.
    SCase "n = S n'".
      apply f_equal.
      apply IHm'.
      inversion H.
      reflexivity.
Qed.

Theorem length_snoc' : forall (X:Type) (v:X) (l:list X) (n:nat),
                         length l = n ->
                         length (snoc l v) = S n.
Proof.
  intros X v l. induction l as [|v' l'].
  Case "l = []".
    intros n H.
    rewrite <- H.
    reflexivity.
  Case "l = v' :: l'".
    intros n H.
    simpl.
    destruct n as [|n'].
    SCase "n = 0". inversion H.
    SCase "n = S n'".
      apply f_equal.
      apply IHl'.
      inversion H.
      reflexivity.
Qed.

Theorem index_after_last : forall (n:nat) (X:Type) (l:list X),
                             length l = n ->
                             index n l = None.
Proof.
  intros n X l.
  generalize dependent n.
  induction l as [| x l'].
  Case "l = []". reflexivity.
  Case "l = x :: l'".
    intros n eq.
    destruct n as [|n'].
    SCase "n = 0". simpl. inversion eq.
    SCase "n = S n'".
      simpl.
      apply IHl'.
      inversion eq.
      reflexivity.
Qed.

Theorem length_snoc'' : forall (n:nat) (X:Type) (v:X) (l:list X),
                          length l = n ->
                          length (snoc l v) = S n.
Proof.
  intros n X v l.
  generalize dependent n.
  induction l as [|x l'].
  Case "l = []".
    intros n eq.
    simpl.
    destruct n as [|n'].
    SCase "n = 0". reflexivity.
    SCase "n = S n'". inversion eq.
  Case "l = x :: l'".
    intros n eq.
    destruct n as [|n'].
    SCase "n = 0". inversion eq.
    SCase "n = S n'".
      simpl.
      apply f_equal.
      rewrite <- IHl'.
      reflexivity.
      inversion eq.
      reflexivity.
Qed.

Theorem app_length_cons : forall (X:Type) (l1 l2 : list X) (x:X) (n:nat),
                            length (l1 ++ (x :: l2)) = n ->
                            S (length (l1 ++ l2)) = n.
Proof.
  intros X l1 l2 x n eq.
  generalize dependent n.
  generalize dependent l2.
  induction l1 as [|x' l1'].
  Case "l1 = []".
    intros n l2 eq.
    simpl.
    destruct n as [|n'].
    SCase "n = 0". inversion eq. reflexivity.
    SCase "n = S n'".
      simpl.
      apply eq.
  Case "l1 = x :: l1'".
    intros l2 n eq.
    destruct n as [|n'].
    SCase "n = 0". inversion eq.
    SCase "n = S n'".
      simpl.
      apply f_equal.
      apply IHl1'.
      inversion eq.
      reflexivity.
Qed.

Definition sillyfun (n:nat) : bool :=
  if beq_nat n 3 then false
  else if beq_nat n 5 then false
       else false.

Theorem sillyfun_false : forall (n:nat),
                           sillyfun n = false.
Proof.
  intros n.
  unfold sillyfun.
  destruct (beq_nat n 3).
  Case "beq_nat n 3 = true". reflexivity.
  Case "beq_nat n 3 = false".
    destruct (beq_nat n 5).
    SCase "beq_nat n 5 = true". reflexivity.
    SCase "beq_nat n 5 = false". reflexivity.
Qed.

Theorem override_shadow :
  forall (X:Type) x1 x2 k1 k2 (f:nat->X),
    (override (override f k1 x2) k1 x1) k2 = (override f k1 x1) k2.
Proof.
  intros X x1 x2 k1 k2 f.
  unfold override.
  destruct (beq_nat k1 k2).
  Case "beq_nat k1 k2 = true". reflexivity.
  Case "beq_nat k1 k2 = false". reflexivity.
Qed.

Theorem combine_split : forall X Y (l:list (X * Y)) l1 l2,
                          split l = (l1, l2) ->
                          combine l1 l2 = l.
Proof.
  intros X Y l l1 l2 eq.
  generalize dependent l1.
  generalize dependent l2.
  induction l as [| [x y] l'].
  Case "l = []".
    intros l1 l2 eq.
    inversion eq.
    reflexivity.
  Case "l = (x, y) :: l'".
    intros l1 l2 eq.
    destruct l1 as [|x' l1'].
    SCase "l1 = []".
      inversion eq.
      destruct (split l') as [xs ys].
      inversion H0.
    SCase "l1 = x' :: l1'".
      inversion eq.
      destruct (split l') as [xs ys].
      inversion H0.
      simpl.
      rewrite -> IHl'.
      reflexivity.
      rewrite -> H3.
      reflexivity.
Qed.

Definition sillyfun1 (n:nat) : bool :=
  if beq_nat n 3 then true
  else if beq_nat n 5 then true
       else false.

Theorem sillyfun1_odd : forall (n:nat),
                          sillyfun1 n = true ->
                          oddb n = true.
Proof.
  intros n eq.
  unfold sillyfun1 in eq.
  destruct (beq_nat n 3) eqn:Heqe3.
  Case "e3 = true".
    apply beq_nat_true in Heqe3.
    rewrite -> Heqe3.
    reflexivity.
  Case "e3 = false".
    destruct (beq_nat n 5) eqn: Heqe5.
    SCase "e5 = true".
      apply beq_nat_true in Heqe5.
      rewrite -> Heqe5.
      reflexivity.
    SCase "e5 = false". inversion eq.
Qed.

Theorem bool_fn_applied_thrice :
  forall (f:bool -> bool) (b : bool),
    f (f (f b)) = f b.
Proof.
  intros f b.
  destruct (f b) eqn: Hfb.
  Case "f b = true".
    destruct b eqn: Hb.
    SCase "b = true".
      rewrite -> Hfb.
      apply Hfb.
    SCase "b = false".
      destruct (f true) eqn: Hftrue.
      SSCase "f true = true". apply Hftrue.
      SSCase "f true = false". apply Hfb.
  Case "f b = false".
    destruct b eqn: Hb.
    SCase "b = true".
      destruct (f false) eqn: Hffalse.
      SSCase "(f false) = tru". apply Hfb.
      SSCase "(f false) = false". apply Hffalse.
    SCase "b = false".
      rewrite -> Hfb.
      apply Hfb.
Qed.

Theorem override_same : forall (X:Type) x1 k1 k2 (f:nat->X),
                          f k1 = x1 ->
                          (override f k1 x1) k2 = f k2.
Proof.
  intros X x1 k1 k2 f eq.
  unfold override.
  destruct (beq_nat k1 k2) eqn: Hk1k2.
  Case "beq_nat k1 k2 = true".
    rewrite <- eq.
    apply f_equal.
    apply beq_nat_true in Hk1k2.
    apply Hk1k2.
  Case "beq_nat k1 k2 = false".
    reflexivity.
Qed.

Theorem beq_nat_sym : forall (n m : nat),
                        beq_nat n m = beq_nat m n.
Proof.
  intros n. induction n as [|n'].
  Case "n = 0".
    intros m. destruct m as [|m'].
    SCase "m = 0". reflexivity.
    SCase "m = S m'". reflexivity.
  Case "n = S n'".
    intros m. destruct m as [|m'].
    SCase "m = 0". reflexivity.
    SCase "m = S m'". simpl. apply IHn'.
Qed.

Theorem beq_nat_trans : forall n m p,
                          beq_nat n m = true ->
                          beq_nat m p = true ->
                          beq_nat n p = true.
Proof.
  intros n m p eq1 eq2.
  apply beq_nat_true in eq1.
  apply beq_nat_true in eq2.
  rewrite trans_eq with (n:=n) (m:=m) (o:=p).
  symmetry.
  apply beq_nat_refl.
  apply eq1.
  apply eq2.
Qed.
