Require Export Logic.

Definition even (n:nat) : Prop :=
  evenb n = true.

Inductive ev : nat -> Prop :=
| ev_0 : ev 0
| ev_SS : forall (n:nat), ev n -> ev (S (S n)).

Theorem double_even : forall n,
                        ev (double n).
Proof.
  intros n. induction n as [|n'].
  Case "n = 0". simpl. apply ev_0.
  Case "n = S n'".
    simpl.
    apply ev_SS.
    apply IHn'.
Qed.

Inductive beautiful : nat -> Prop :=
| b_0 : beautiful 0
| b_3 : beautiful 3
| b_5 : beautiful 5
| b_sum : forall (n m : nat), beautiful n -> beautiful m -> beautiful (n + m).

Theorem three_is_beautiful : beautiful 3.
Proof.
  apply b_3.
Qed.

Theorem eight_is_beautiful : beautiful 8.
Proof.
  apply b_sum with (n:=3) (m:=5).
  apply b_3.
  apply b_5.
Qed.

Theorem beautiful_plus_eight : forall n, beautiful n -> beautiful (8 + n).
Proof.
  intros n B.
  apply b_sum.
  apply eight_is_beautiful.
  apply B.
Qed.

Theorem b_times2 : forall n, beautiful n -> beautiful (2 * n).
Proof.
  intros n B.
  simpl.
  apply b_sum.
  apply B.
  rewrite -> plus_O_r.
  apply B.
Qed.

Theorem b_timesm : forall n m, beautiful n -> beautiful (m * n).
Proof.
  intros n m B.
  induction m as [|m'].
  Case "m = 0".
    simpl.
    apply b_0.
  Case "m = S m'".
    simpl.
    apply b_sum.
    apply B.
    apply IHm'.
Qed.

Inductive gorgeous : nat -> Prop :=
| g_0 : gorgeous 0
| g_plus3 : forall n, gorgeous n -> gorgeous (3 + n)
| g_plus5 : forall n, gorgeous n -> gorgeous (5 + n).

Theorem gorgeous_plus13 : forall n,
                            gorgeous n -> gorgeous (13 + n).
Proof.
  intros n G.
  induction G.
  Case "g_0".
    simpl.
    apply g_plus5.
    apply g_plus5.
    apply g_plus3.
    apply g_0.
  Case "g_plus3".
    apply g_plus3.
    apply IHG.
  Case "g_plus5".
    apply g_plus5.
    apply IHG.
Qed.

Theorem gorgeous__beautiful : forall n,
                                gorgeous n -> beautiful n.
Proof.
  intros n H.
  induction H as [|n'|n'].
  Case "g_0".
    apply b_0.
  Case "g_plus3".
    apply b_sum.
    apply b_3.
    apply IHgorgeous.
  Case "g_plus5".
    apply b_sum.
    apply b_5.
    apply IHgorgeous.
Qed.

Theorem gorgeous_sum : forall n m,
                         gorgeous n -> gorgeous m -> gorgeous (n + m).
Proof.
  intros n m Gn Gm.
  induction Gn.
  Case "g_0".
    simpl.
    apply Gm.
  Case "g_plus3".
    simpl.
    apply g_plus3.
    apply IHGn.
  Case "g_plus5".
    simpl.
    apply g_plus5.
    apply IHGn.
Qed.

Theorem beautiful__gorgeous : forall n, beautiful n -> gorgeous n.
Proof.
  intros n B.
  induction B.
  Case "b_0".
    apply g_0.
  Case "b_3".
    apply g_plus3.
    apply g_0.
  Case "b_5".
    apply g_plus5.
    apply g_0.
  Case "b_sum".
    apply gorgeous_sum.
    apply IHB1.
    apply IHB2.
Qed.

Lemma helper_g_times2 : forall x y z, x + (z + y) = z + x + y.
Proof.
  intros x y z.
  rewrite -> (plus_comm z x).
  rewrite -> plus_assoc.
  reflexivity.
Qed.

Theorem g_times2 : forall n, gorgeous n -> gorgeous (2 * n).
Proof.
  intros n H.
  simpl.
  induction H.
  Case "g_0".
    simpl.
    apply g_0.
  Case "g_plus3".
    rewrite -> plus_O_r.
    rewrite -> helper_g_times2.
    simpl.
    apply g_plus3.
    apply g_plus3.
    rewrite -> plus_O_r in IHgorgeous.
    apply IHgorgeous.
  Case "g_plus5".
    rewrite -> plus_O_r.
    rewrite -> helper_g_times2.
    simpl.
    apply g_plus5.
    apply g_plus5.
    rewrite -> plus_O_r in IHgorgeous.
    apply IHgorgeous.
Qed.

Theorem ev__even : forall n,
                     ev n -> even n.
Proof.
  intros n E. induction E as [|n' E'].
  Case "ev_0".
    reflexivity.
  Case "ev_SS n' E'".
    apply IHE'.
Qed.

Theorem ev_sum : forall n m,
                   ev n -> ev m -> ev (n + m).
Proof.
  intros n m En Em.
  induction En.
  Case "e_0".
    simpl.
    apply Em.
  Case "e_SS".
    simpl.
    apply ev_SS.
    apply IHEn.
Qed.

Theorem ev_minus2 : forall n, ev n -> ev (pred (pred n)).
Proof.
  intros n E.
  inversion E as [|n' E'].
  Case "ev_0". simpl. apply ev_0.
  Case "eb_SS n' E'". simpl. apply E'.
Qed.

Theorem SSev__even : forall n,
                       ev (S (S n)) -> ev n.
Proof.
  intros n E.
  inversion E as [|n' E'].
  apply E'.
Qed.

Theorem SSSSev__even : forall n,
                         ev (S (S (S (S n)))) -> ev n.
Proof.
  intros n E.
  inversion E as [|n' E'].
  apply SSev__even in E'.
  apply E'.
Qed.

Theorem even5_nonsense :
  ev 5 -> 2 + 2 = 9.
Proof.
  intros E.
  inversion E.
  inversion H0.
  inversion H2.
Qed.

Theorem ev_ev__ev : forall n m,
                      ev (n + m) -> ev n -> ev m.
Proof.
  intros n m Enm En.
  generalize dependent Enm.
  induction En.
  Case "ev (0 + m)".
  intros Enm.
  simpl in Enm.
  apply Enm.
  Case "ev ((S (S n)) + m)".
  intros Enm.
  inversion Enm.
  apply IHEn in H0.
  apply H0.
Qed.

Inductive ev_list {X:Type} : list X -> Prop :=
| el_nil : ev_list []
| el_cc : forall x y l, ev_list l -> ev_list (x :: y :: l).

Lemma ev_list__ev_length : forall X (l:list X),
                             ev_list l -> ev (length l).
Proof.
  intros X l H. induction H.
  Case "el_nil". simpl. apply ev_0.
  Case "el_cc".
    simpl.
    apply ev_SS.
    apply IHev_list.
Qed.

Inductive pal {X:Type} : list X -> Prop :=
| pal_e : pal []
| pal_x : forall x, pal [x]
| pal_xpx : forall x p, pal p -> pal ((x :: p) ++ [x]).

Inductive le : nat -> nat -> Prop :=
| le_n : forall n, le n n
| le_S : forall n m, (le n m) -> (le n (S m)).

Notation "m <= n" := (le m n).

Theorem test_le1 : 3 <= 3.
Proof. apply le_n. Qed.
Theorem test_le2 : 3 <= 6.
Proof. apply le_S. apply le_S. apply le_S. apply le_n. Qed.
Theorem test_le3 : (2 <= 1) -> 2 + 2 = 5.
Proof. intros H. inversion H. inversion H2. Qed.

Definition lt (n m : nat) := le (S n) m.

Notation "m < n" := (lt m n).

Inductive square_of : nat -> nat -> Prop :=
  sq : forall (n:nat), square_of n (n * n).

Inductive next_nat : nat -> nat -> Prop :=
| nn : forall (n:nat), next_nat n (S n).

Inductive next_even : nat -> nat -> Prop :=
| ne_1 : forall n, ev (S n) -> next_even n (S n)
| ne_2 : forall n, ev (S (S n)) -> next_even n (S (S n)).

Lemma le_trans : forall m n o, m <= n -> n <= o -> m <= o.
Proof.
  intros m n o Hmn Hno.
  induction Hno.
  apply Hmn.
  apply le_S.
  apply IHHno.
  apply Hmn.
Qed.

Theorem O_le_n : forall n,
                   0 <= n.
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0".
    apply le_n.
  Case "n = S n'".
    apply le_S.
    apply IHn'.
Qed.

Theorem n_le_m__Sn_le_Sm : forall n m,
                             n <= m -> S n <= S m.
Proof.
  intros n m H. induction H.
  Case "le_n". apply le_n.
  Case "le_S".
    apply le_S.
    apply IHle.
Qed.

Theorem Sn_le_Sm__n_le_m : forall n m,
                             S n <= S m -> n <= m.
Proof.
  intros n m H. inversion H.
  apply le_n.
  apply le_trans with (n := S n).
  apply le_S.
  apply le_n.
  apply H2.
Qed.

Theorem le_plus_l : forall a b,
                      a <= a + b.
Proof.
  intros a b. induction a as [|a'].
  Case "a = 0". apply O_le_n.
  Case "a = S a'".
    simpl.
    apply n_le_m__Sn_le_Sm.
    apply IHa'.
Qed.

Theorem plus_lt : forall n1 n2 m,
                    n1 + n2 < m ->
                    n1 < m /\ n2 < m.
Proof.
  intros n1 n2 m.
  unfold lt.
  intros H.
  split.
  apply le_trans with (n := S (n1 + n2)).
  rewrite -> plus_comm.
  rewrite plus_n_Sm.
  rewrite plus_comm.
  apply le_plus_l.
  apply H.
  apply le_trans with (n := S (n1 + n2)).
  rewrite plus_n_Sm.
  rewrite -> plus_comm.
  apply le_plus_l.
  apply H.
Qed.

Theorem lt_S : forall n m,
               n < m ->
               n < S m.
Proof.
  intros n m.
  unfold lt.
  intros H.
  apply le_S.
  apply H.
Qed.

Theorem ble_nat_true : forall n m,
                         ble_nat n m = true ->
                         n <= m.
Proof.
  intros n. induction n as [|n'].
  Case "n = 0".
    intros m H.
    apply O_le_n.
  Case "n = S n'".
    intros m H.
    destruct m as [| m'].
    SCase "m = 0". inversion H.
    SCase "m = S m'".
      apply n_le_m__Sn_le_Sm.
      apply IHn'.
      apply H.
Qed.

Theorem le_ble_nat : forall n m,
                       n <= m ->
                       ble_nat n m = true.
Proof.
  intros n m.
  generalize dependent n.
  induction m as [|m'].
  Case "m = 0".
    intros n H.
    inversion H.
    reflexivity.
  Case "m = S m'".
    intros n H.
    inversion H.
    symmetry.
    apply ble_nat_refl.
    destruct n as [|n'].
    SCase "n = 0". reflexivity.
    SCase "n = S n'".
      simpl.
      apply IHm'.
      apply Sn_le_Sm__n_le_m.
      apply H.
Qed.

Theorem ble_nat_true_trans :
  forall n m o,
    ble_nat n m = true -> ble_nat m o = true -> ble_nat n o = true.
Proof.
  intros n m o H1 H2.
  apply le_ble_nat.
  apply ble_nat_true in H1.
  apply ble_nat_true in H2.
  apply le_trans with (n := m).
  apply H1.
  apply H2.
Qed.

Theorem ble_nat_false : forall n m,
                          ble_nat n m = false -> ~(n <= m).
Proof.
  intros n m H1.
  unfold not.
  intros H2.
  apply le_ble_nat in H2.
  rewrite H1 in H2.
  inversion H2.
Qed.
