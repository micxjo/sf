Require Export "Prop".

Inductive ex (X:Type) (P : X -> Prop) : Prop :=
  ex_intro : forall (witness : X), P witness -> ex X P.

Notation "'exists' x , p" :=
  (ex _ (fun x => p))
    (at level 200, x ident, right associativity) : type_scope.
Notation "'exists' x : X , p" :=
  (ex _ (fun x:X => p))
    (at level 200, x ident, right associativity) : type_scope.

Example exists_example_1 : exists n, n + (n * n) = 6.
Proof.
  apply ex_intro with (witness:=2).
  reflexivity.
Qed.

Example exists_example1' : exists n, n + (n * n) = 6.
Proof.
  exists 2.
  reflexivity.
Qed.

Theorem exists_example_2 : forall n,
                             (exists m, n = 4 + m) ->
                             (exists o, n = 2 + o).
Proof.
  intros n H.
  inversion H as [m Hm].
  exists (2 + m).
  apply Hm.
Qed.

Lemma exists_example_3 :
  exists (n : nat), even n /\ beautiful n.
Proof.
  exists 8.
  split.
  unfold even.
  simpl.
  reflexivity.
  apply b_sum with (n:=3) (m:=5).
  apply b_3.
  apply b_5.
Qed.

Theorem dist_not_exists : forall (X:Type) (P : X -> Prop),
                            (forall x, P x) -> ~(exists x, ~ P x).
Proof.
  intros X P H1.
  unfold not.
  intros H2.
  inversion H2 as [x Hx].
  apply Hx.
  apply H1.
Qed.

Theorem dist_exists_or :
  forall (X:Type) (P Q : X -> Prop),
    (exists x, P x \/ Q x) <-> (exists x, P x) \/ (exists x, Q x).
Proof.
  intros X P Q.
  split.
  intros H.
  inversion H as [x Hx].
  inversion Hx.
  left.
  exists x.
  apply H0.
  right.
  exists x.
  apply H0.
  intros H.
  inversion H.
  inversion H0 as [x Hx].
  exists x.
  left.
  apply Hx.
  inversion H0 as [x Hx].
  exists x.
  right.
  apply Hx.
Qed.
