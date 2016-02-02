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
