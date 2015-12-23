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

Notation "( x , y )" := (pair x y).
Notation "X * Y" := (prod X Y) : type_scope.

Definition fst {X Y : Type} (p : X * Y) : X :=
  match p with (x,y) => x end.

Definition snd {X Y : Type} (p: X * Y) : Y :=
  match p with (x,y) => y end.

Fixpoint combine {X Y : Type} (lx : list X) (ly : list Y) : list (X * Y) :=
  match (lx, ly) with
    | ([], _) => []
    | (_, []) => []
    | (x::tx, y::ty) => (x, y) :: (combine tx ty)
  end.

Fixpoint split {X Y : Type} (l : list (X * Y)) : (list X) * (list Y) :=
  match l with
    | nil => (nil, nil)
    | (x, y) :: lxs => match split lxs with
                         | (xs, ys) => (x :: xs, y :: ys)
                       end
  end.

Example test_split: split [(1, false); (2, false)] = ([1;2], [false;false]).
Proof. reflexivity. Qed.

Inductive option (X:Type) : Type :=
| Some : X -> option X
| None : option X.

Arguments Some {X} _.
Arguments None {X}.

Fixpoint index {X:Type} (n:nat) (l:list X) : option X :=
  match l with
    | [] => None
    | a :: l' => if beq_nat n 0 then Some a else index (pred n) l'
  end.

Example test_index1 : index 0 [4;5;6;7] = Some 4.
Proof. reflexivity. Qed.
Example test_index2 : index 1 [[1];[2]] = Some [2].
Proof. reflexivity. Qed.
Example test_index3 : index 2 [true] = None.
Proof. reflexivity. Qed.

Definition hd_opt {X:Type} (l:list X) : option X :=
  match l with
    | nil => None
    | x :: t => Some x
  end.

Example test_hd_opt1 : hd_opt [1;2] = Some 1.
Proof. reflexivity. Qed.
Example test_hd_opt2 : hd_opt [[1];[2]] = Some [1].
Proof. reflexivity. Qed.

Definition prod_curry {X Y Z : Type}
           (f : X * Y -> Z) (x:X) (y:Y) : Z := f (x, y).

Definition prod_uncurry {X Y Z : Type}
           (f : X -> Y -> Z) (p: X * Y) : Z :=
  f (fst p) (snd p).

Theorem uncurry_curry : forall (X Y Z : Type) (f : X -> Y -> Z) x y,
                          prod_curry (prod_uncurry f) x y = f x y.
Proof.
  intros X Y Z f x y.
  reflexivity.
Qed.

Theorem curry_uncurry : forall (X Y Z : Type) (f: (X * Y) -> Z) (p: X * Y),
                          prod_uncurry (prod_curry f) p = f p.
Proof.
  intros X Y Z f p.
  simpl.
  destruct p.
  reflexivity.
Qed.

Fixpoint filter {X:Type} (test : X -> bool) (l:list X) : (list X) :=
  match l with
    | nil => nil
    | h :: t => if test h
                then h :: (filter test t)
                else filter test t
  end.

Example test_filter1: filter evenb [1;2;3;4] = [2;4].
Proof. reflexivity. Qed.

Definition length_is_1 {X:Type} (l:list X) : bool :=
  beq_nat (length l) 1.

Example test_filter2:
  filter length_is_1 [[1;2]; [3]; [4]; [5;6;7]; []; [8]]
  = [[3]; [4]; [8]].
Proof. reflexivity. Qed.

Definition filter_even_gt7 (l:list nat) : list nat :=
  filter (fun n => andb (evenb n) (negb (ble_nat n 7))) l.

Example test_filter_even_gt7_1 :
  filter_even_gt7 [1;2;6;9;10;3;12;8] = [10;12;8].
Proof. reflexivity. Qed.
Example test_filter_even_gt7_2 :
  filter_even_gt7 [5;2;6;19;129] = [].
Proof. reflexivity. Qed.

Definition partition {X:Type} (test:X -> bool) (l:list X) : list X * list X :=
  (filter test l, filter (fun x => negb (test x)) l).

Example test_partition1: partition oddb [1;2;3;4;5] = ([1;3;5], [2;4]).
Proof. reflexivity. Qed.
Example test_partition2: partition (fun x => false) [5;9;0] = ([], [5;9;0]).
Proof. reflexivity. Qed.

Fixpoint map {X Y:Type} (f:X -> Y) (l:list X) : (list Y) :=
  match l with
    | [] => []
    | h :: t => (f h) :: (map f t)
  end.

Lemma snoc_append : forall (X:Type) (l:list X) (x:X),
                      snoc l x = l ++ [x].
Proof.
  intros X l x. induction l as [|x' l'].
  Case "l = []". reflexivity.
  Case "l = x' :: l'".
  simpl.
  rewrite -> IHl'.
  reflexivity.
Qed.

Lemma map_app : forall (X Y:Type) (f:X -> Y) (l1 l2:list X),
                  map f (l1 ++ l2) = map f l1 ++ map f l2.
Proof.
  intros X Y f l1 l2.
  induction l1 as [|x l1'].
  Case "l1 = []". reflexivity.
  Case "l1 = x :: l1'".
    simpl.
    rewrite -> IHl1'.
    reflexivity.
Qed.

 Theorem map_rev : forall (X Y : Type) (f:X -> Y) (l:list X),
                    map f (rev l) = rev (map f l).
Proof.
  intros X Y f l. induction l as [| x l'].
  Case "l = []". reflexivity.
  Case "l = x :: l'".
    simpl.
    repeat rewrite -> snoc_append.
    rewrite -> map_app.
    rewrite -> IHl'.
    reflexivity.
Qed.

Fixpoint flat_map {X Y:Type} (f:X -> list Y) (l:list X) : (list Y) :=
  match l with
    | [] => []
    | x :: xs => f x ++ flat_map f xs
  end.

Example test_flat_map1:
  flat_map (fun n => [n;n;n]) [1;5;4]
  = [1; 1; 1; 5; 5; 5; 4; 4; 4].
Proof. reflexivity. Qed.

Definition option_map {X Y:Type} (f:X -> Y) (xo:option X) : option Y :=
  match xo with
    | None => None
    | Some x => Some (f x)
  end.

Fixpoint fold {X Y:Type} (f:X -> Y -> Y) (l:list X) (b:Y) : Y :=
  match l with
    | [] => b
    | h :: t => f h (fold f t b)
  end.

Example fold_example1 : fold mult [1;2;3;4] 1 = 24.
Proof. reflexivity. Qed.

Example fold_example2 : fold andb [true;true;false;true] true = false.
Proof. reflexivity. Qed.

Example fold_example3 : fold app [[1];[];[2;3];[4]] [] = [1;2;3;4].
Proof. reflexivity. Qed.

Definition constfun {X:Type} (x:X) : nat -> X :=
  fun (k:nat) => x.

Definition ftrue := constfun true.
Definition ffalse := constfun false.

Definition override {X:Type} (f:nat->X) (k:nat) (x:X) : nat -> X :=
  fun (k':nat) => if beq_nat k k' then x else f k'.

Theorem override_example : forall (b:bool),
                             (override (constfun b) 3 true) 2 = b.
Proof.
  intros b; destruct b; reflexivity.
Qed.

Theorem override_eq :
  forall {X:Type} x k (f:nat->X),
    (override f k x) k = x.
Proof.
  intros X x k f.
  unfold override.
  rewrite <- beq_nat_refl.
  reflexivity.
Qed.

Theorem override_neq :
  forall (X:Type) x1 x2 k1 k2 (f:nat->X),
    f k1 = x1 ->
    beq_nat k2 k1 = false ->
    (override f k2 x2) k1 = x1.
Proof.
  intros X x1 x2 k1 k2 f H1 H2.
  unfold override.
  rewrite -> H2.
  rewrite -> H1.
  reflexivity.
Qed.

Definition fold_length {X:Type} (l:list X) : nat :=
  fold (fun _ n => S n) l 0.

Theorem fold_length_correct : forall X (l:list X),
                                fold_length l = length l.
Proof.
  intros X l. induction l as [| x l'].
  Case "l = []".
    reflexivity.
  Case "l = x :: l'".
    simpl.
    rewrite <- IHl'.
    reflexivity.
Qed.

Definition fold_map {X Y:Type} (f:X->Y) (l:list X) : list Y :=
  fold (fun x acc => f x :: acc) l [].

Theorem fold_map_correct :
  forall X Y (f:X->Y) (l:list X),
    fold_map f l = map f l.
Proof.
  intros X Y f l. induction l as [| x l'].
  Case "l = []". reflexivity.
  Case "l = x :: l'".
    simpl.
    rewrite <- IHl'.
    reflexivity.
Qed.

Module Church.

  Definition nat := forall X : Type, (X -> X) -> X -> X.

  Definition one : nat :=
    fun (X:Type) (f:X->X) (x:X) => f x.

  Definition two : nat :=
    fun (X:Type) (f:X->X) (x:X) => f (f x).

  Definition three : nat :=
    fun (X:Type) (f:X->X) (x:X) => f (f (f x)).

  Definition zero : nat :=
    fun (X:Type) (f:X->X) (x:X) => x.

  Definition succ (n:nat) : nat :=
    fun (X:Type) (f:X->X) (x:X) => f (n X f x).

  Example succ_1 : succ zero = one.
  Proof. reflexivity. Qed.
  Example succ_2 : succ one = two.
  Proof. reflexivity. Qed.
  Example succ_3 : succ two = three.
  Proof. reflexivity. Qed.

  Definition plus (n m : nat) : nat :=
    fun (X:Type) (f:X->X) (x:X) => m X f (n X f x).

  Example plus_1 : plus zero one = one.
  Proof. reflexivity. Qed.
  Example plus_2 : plus two three = plus three two.
  Proof. reflexivity. Qed.
  Example plus_3 : plus (plus two two) three = plus one (plus three three).
  Proof. reflexivity. Qed.

  Definition mult (n m : nat) : nat :=
    fun (X:Type) (f:X->X) (x:X) => m X (n X f) x.

  Example mult_1 : mult one one = one.
  Proof. reflexivity. Qed.
  Example mult_2 : mult zero (plus three three) = zero.
  Proof. reflexivity. Qed.
  Example mult_3 : mult two three = plus three three.
  Proof. reflexivity. Qed.

End Church.