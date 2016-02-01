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

Inductive sumbool (A B : Prop) : Set :=
| left : A -> sumbool A B
| right : B -> sumbool A B.

Notation "{ A } + { B }" := (sumbool A B) : type_scope.

Theorem eq_nat_dec : forall n m : nat, {n = m} + {n <> m}.
Proof.
  intros n.
  induction n as [|n'].
  Case "n = 0".
    intros m.
    destruct m as [|m'].
    SCase "m = 0".
      left.
      reflexivity.
    SCase "m = S m'".
      right.
      intros contra.
      inversion contra.
  Case "n = S n'".
    intros m.
    destruct m as [|m'].
    SCase "m = 0".
      right.
      intros contra.
      inversion contra.
    SCase "m = S m'".
      destruct IHn' with (m:=m') as [eq|neq].
      left.
      apply f_equal.
      apply eq.
      right.
      intros Heq.
      inversion Heq as [Heq'].
      apply neq.
      apply Heq'.
Defined.

Definition override' {X:Type} (f:nat->X) (k:nat) (x:X) : nat->X :=
  fun (k':nat) => if eq_nat_dec k k' then x else f k'.

Theorem override_same' : forall (X:Type) x1 k1 k2 (f:nat->X),
                           f k1 = x1 ->
                           (override' f k1 x1) k2 = f k2.
Proof.
  intros X x1 k1 k2 f Hx1.
  unfold override'.
  destruct (eq_nat_dec k1 k2).
  Case "k1 = k2".
    rewrite <- e.
    symmetry.
    apply Hx1.
  Case "k1 <> k2".
    reflexivity.
Qed.

Theorem override_shadow' :
  forall (X:Type) x1 x2 k1 k2 (f:nat->X),
    (override' (override' f k1 x2) k1 x1) k2 = (override' f k1 x1) k2.
Proof.
  intros X x1 x2 k1 k2 f.
  unfold override'.
  destruct (eq_nat_dec k1 k2).
  Case "k1 = k2".
    reflexivity.
  Case "k1 <> k2".
    reflexivity.
Qed.

Inductive all (X:Type) (P:X->Prop) : list X -> Prop :=
| all_nil : all X P nil
| all_cons : forall x l, P x -> all X P l -> all X P (x :: l).

Fixpoint forallb {X:Type} (test:X->bool) (l:list X) : bool :=
  match l with
    | [] => true
    | x :: l' => andb (test x) (forallb test l')
  end.

Theorem forallb_all : forall (X:Type) (f:X->bool) (l:list X),
                        all X (fun x => f x = true) l <-> forallb f l = true.
Proof.
  intros X f l.
  split.
  Case "->".
    intros H.
    induction H.
    reflexivity.
    simpl.
    rewrite -> IHall.
    rewrite -> H.
    reflexivity.
  Case "<-".
    intros H.
    induction l as [|x l'].
    SCase "l = []".
      apply all_nil.
    SCase "l = x :: l'".
      simpl in H.
      apply all_cons.
      apply andb_true_elim1 in H.
      apply H.
      apply IHl'.
      apply andb_true_elim2 in H.
      apply H.
Qed.

Inductive nostutter: list nat -> Prop :=
| ns_nil : nostutter []
| ns_one : forall x, nostutter [x]
| ns_two : forall x1 x2 l, x1 <> x2 ->
                           nostutter (x2 :: l) ->
                           nostutter (x1 :: x2 :: l).

Example test_nostutter_1: nostutter [3;1;4;1;5;6].
Proof.
  repeat constructor; apply beq_nat_false; auto.
Qed.

Example test_nostutter_2: nostutter [].
Proof.
  repeat constructor; apply beq_nat_false; auto.
Qed.

Example test_nostutter_3: nostutter [5].
Proof.
  repeat constructor; apply beq_nat_false; auto.
Qed.

Example test_nostutter_4: not (nostutter [3;1;1;4]).
Proof.
  intro.
  repeat match goal with
             h: nostutter _ |- _ => inversion h; clear h; subst
         end.
  contradiction H1; auto.
Qed.
