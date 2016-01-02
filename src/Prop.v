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

Lemma ev_length__ev_list :
  forall X n,
    ev n -> forall (l:list X), n = length l -> ev_list l.
Proof.
  intros X n H.
  induction H.
  Case "ev_0".
    intros l H.
    destruct l.
    SCase "[]". apply el_nil.
    SCase "x :: l". inversion H.
  Case "ev_SS".
    intros l H2.
    destruct l.
    SCase "[]".
      inversion H2.
      destruct l.
    SCase "[x]".
      inversion H2.
      destruct l.
    SCase "x :: x0 :: l".
      apply el_cc.
      apply IHev.
      inversion H2.
      reflexivity.
Qed.
