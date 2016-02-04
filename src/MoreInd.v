Require Export "ProofObjects".

Theorem mult_O_r' : forall n:nat, n * 0 = 0.
Proof.
  apply nat_ind.
  Case "0". reflexivity.
  Case "S".
    simpl.
    intros n IHn.
    rewrite -> IHn.
    reflexivity.
Qed.

Theorem plus_one_r' : forall n : nat, n + 1 = S n.
Proof.
  apply nat_ind.
  Case "0". reflexivity.
  Case "S".
    simpl.
    intros n IHn.
    rewrite -> IHn.
    reflexivity.
Qed.

Inductive mytype (X:Type) : Type :=
| constr1 : X -> mytype X
| constr2 : nat -> mytype X
| constr3 : mytype X -> nat -> mytype X.

Inductive foo (X Y : Type) : Type :=
| bar : X -> foo X Y
| baz : Y -> foo X Y
| quux : (nat -> foo X Y) -> foo X Y.

Lemma one_not_beautiful : forall n, n = 1 -> ~ beautiful n.
Proof.
  intros n E H.
  induction H as [| | | p q Hp IHp Hq IHq].
  Case "b_O". inversion E.
  Case "b_3". inversion E.
  Case "b_5". inversion E.
  Case "b_sum".
    destruct p as [|p'].
    SCase "p = 0".
      destruct q as [|q'].
      SSCase "q = 0". inversion E.
      SSCase "q = S q'".
        apply IHq.
        apply E.
    SCase "p = S p'".
      destruct q as [|q'].
      SSCase "q = 0".
        apply IHp.
        rewrite -> plus_O_r in E.
        apply E.
      SSCase "q = S q'".
        simpl in E.
        inversion E.
        destruct p'.
        inversion H0.
        inversion H0.
Qed.

Lemma one_not_beautiful': ~ beautiful 1.
Proof.
  intros H.
  remember 1 as n eqn:E.
  induction H.
Admitted.
