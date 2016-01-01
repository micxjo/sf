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
