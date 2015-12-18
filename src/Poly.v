Require Export Lists.

Inductive list (X:Type) : Type :=
| nil : list X
| cons : X -> list X -> list X.

Fixpoint length (X:Type) (l:list X) : nat :=
  match l with
    | nil => 0
    | cons h t => S (length X t)
  end.


Fixpoint app (X:Type) (l1 l2 : list X) :=
  match l1 with
    | nil => l2
    | cons h t => cons X h (app X t l2)
  end.

Fixpoint snoc (X:Type) (l:list X) (v:X) : (list X) :=
  match l with
    | nil => cons X v (nil X)
    | cons h t => cons X h (snoc X t v)
  end.

Fixpoint rev (X:Type) (l:list X) : list X :=
  match l with
    | nil => nil X
    | cons h t => snoc X (rev X t) h
  end.

Fixpoint app' X l1 l2 : list X :=
  match l1 with
    | nil => l2
    | cons h t => cons X h (app' X t l2)
  end.

Fixpoint length' (X:Type) (l:list X) : nat :=
  match l with
    | nil => 0
    | cons h t => S (length' _ t)
  end.

Arguments nil {X}.
Arguments cons {X} _ _.
Arguments length {X} l.
Arguments app {X} l1 l2.
Arguments rev {X} l.
Arguments snoc {X} l v.

Fixpoint length'' {X:Type} (l:list X) : nat :=
  match l with
    | nil => 0
    | cons h t => S (length'' t)
  end.

Notation "x :: y" := (cons x y)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y []) ..).
Notation "x ++ y" := (app x y)
                     (at level 60, right associativity).

Fixpoint repeat {X:Type} (n:X) (count:nat) : list X :=
  match count with
    | 0 => []
    | 1 => [n]
    | S x => n :: (repeat n x)
  end.

Example test_repeat1:
  repeat true 2 = cons true (cons true nil).
Proof. reflexivity. Qed.

Theorem nil_app : forall X:Type, forall l:list X,
                    app [] l = l.
Proof.
  intros X l.
  reflexivity.
Qed.

Theorem rev_snoc :
  forall X:Type, forall v:X, forall s:list X,
    rev (snoc s v) = v :: (rev s).
Proof.
  intros X v s. induction s as [|v' s'].
  Case "s = nil". reflexivity.
  Case "s = v' :: s'".
    simpl.
    rewrite -> IHs'.
    reflexivity.
Qed.

Theorem rev_involutive : forall X:Type, forall l:list X,
                           rev (rev l) = l.
Proof.
  intros X l. induction l as [|x l'].
  Case "l = nil". reflexivity.
  Case "l = x :: l'".
    simpl.
    rewrite -> rev_snoc. rewrite -> IHl'.
    reflexivity.
Qed.

Theorem snoc_with_append :
  forall X:Type, forall l1 l2 : list X, forall v : X,
    snoc (l1 ++ l2) v = l1 ++ (snoc l2 v).
Proof.
  intros X l1 l2 v. induction l1 as [|x l1'].
  Case "l1 = nil". reflexivity.
  Case "l2 = x :: l1'".
    simpl.
    rewrite -> IHl1'.
    reflexivity.
Qed.

Inductive prod (X Y : Type) : Type :=
  pair : X -> Y -> prod X Y.

Arguments pair {X} {Y} _ _.
