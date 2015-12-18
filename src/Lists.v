Require Export Induction.

Module NatList.

  Inductive natprod : Type :=
    pair : nat -> nat -> natprod.

  Definition fst (p:natprod) : nat :=
    match p with
      | pair x _ => x
    end.

  Definition snd (p:natprod) : nat :=
    match p with
      | pair _ y => y
    end.

  Notation "( x , y )" := (pair x y).

  Definition swap_pair (p:natprod) : natprod :=
    match p with
      | (x,y) => (y,x)
    end.

  Theorem surjective_pairing' : forall (n m : nat),
                                  (n, m) = (fst (n, m), snd (n, m)).
  Proof.
    reflexivity.
  Qed.

  Theorem surjective_pairing : forall (p : natprod),
                                 p = (fst p, snd p).
  Proof.
    intros p. destruct p as [n m]. reflexivity.
  Qed.

  Theorem snd_fst_is_swap : forall (p : natprod),
                              (snd p, fst p) = swap_pair p.
  Proof.
    intros p. destruct p as [n m]. reflexivity.
  Qed.

  Theorem fst_swap_is_snd : forall (p : natprod),
                              fst (swap_pair p) = snd p.
  Proof.
    intros p. destruct p as [n m]. reflexivity.
  Qed.

  Inductive natlist : Type :=
  | nil : natlist
  | cons : nat -> natlist -> natlist.

  Notation "x :: l" := (cons x l) (at level 60, right associativity).
  Notation "[ ]" := nil.
  Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

  Fixpoint repeat (n count : nat) : natlist :=
    match count with
      | 0 => nil
      | S count' => n :: (repeat n count')
    end.

  Fixpoint length (l:natlist) : nat :=
    match l with
      | nil => 0
      | h :: t => S (length t)
    end.

  Fixpoint app (l1 l2 : natlist) : natlist :=
    match l1 with
      | nil => l2
      | h :: t => h :: (app t l2)
    end.

  Notation "x ++ y" := (app x y) (right associativity, at level 60).

  Definition hd (default:nat) (l:natlist) : nat :=
    match l with
      | nil => default
      | h :: t => h
    end.

  Definition tl (l:natlist) : natlist :=
    match l with
      | nil => nil
      | h :: t => t
    end.

  Fixpoint nonzeros (l:natlist) : natlist :=
    match l with
      | nil => nil
      | 0 :: t => nonzeros t
      | n :: t => n :: (nonzeros t)
    end.

  Example test_nonzeros: nonzeros [0;1;0;2;3;0;0] = [1;2;3].
  Proof. reflexivity. Qed.

  Fixpoint oddmembers (l:natlist) : natlist :=
    match l with
      | nil => nil
      | n :: t => if oddb n then n :: (oddmembers t) else oddmembers t
    end.

  Example test_oddmembers : oddmembers [0;1;0;2;3;0;0] = [1;3].
  Proof. reflexivity. Qed.

  Fixpoint countoddmembers (l:natlist) : nat :=
    match l with
      | nil => 0
      | n :: t => if oddb n then 1 + (countoddmembers t) else countoddmembers t
    end.

  Example test_countoddmembers1: countoddmembers [1;0;3;1;4;5] = 4.
  Proof. reflexivity. Qed.
  Example test_countoddmembers2: countoddmembers [0;2;4] = 0.
  Proof. reflexivity. Qed.

  Fixpoint alternate (l1 l2 : natlist) : natlist :=
    match l1, l2 with
      | nil, _ => l2
      | _, nil => l1
      | h :: t, h' :: t' => h :: h' :: (alternate t t')
    end.

  Example test_alternate1: alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
  Proof. reflexivity. Qed.
  Example test_alternate2: alternate [1] [4;5;6] = [1;4;5;6].
  Proof. reflexivity. Qed.
  Example test_alternate3: alternate [1;2;3] [4] = [1;4;2;3].
  Proof. reflexivity. Qed.
  Example test_alternate4: alternate [] [20;30] = [20;30].
  Proof. reflexivity. Qed.

  Definition bag := natlist.

  Fixpoint count (v:nat) (s:bag) : nat :=
    match s with
      | nil => 0
      | h :: t => if beq_nat h v then 1 + (count v t) else count v t
    end.

  Example test_count1: count 1 [1;2;3;1;4;1] = 3.
  Proof. reflexivity. Qed.
  Example test_count2: count 6 [1;2;3;1;4;1] = 0.
  Proof. reflexivity. Qed.

  Definition sum : bag -> bag -> bag :=
    app.

  Example test_sum1: count 1 (sum [1;2;3] [1;4;1]) = 3.
  Proof. reflexivity. Qed.

  Definition add (v:nat) (s:bag) : bag :=
    v :: s.

  Example test_add1: count 1 (add 1 [1;4;1]) = 3.
  Proof. reflexivity. Qed.
  Example test_add2: count 5 (add 1 [1;4;1]) = 0.
  Proof. reflexivity. Qed.

  Definition member (v:nat) (s:bag) : bool :=
    negb (beq_nat (count v s) 0).

  Example test_member1: member 1 [1;4;1] = true.
  Proof. reflexivity. Qed.
  Example test_member2: member 2 [1;4;1] = false.
  Proof. reflexivity. Qed.

  Fixpoint remove_one (v:nat) (s:bag) : bag :=
    match s with
      | nil => nil
      | h :: t => if beq_nat h v then t else h :: remove_one v t
    end.

  Example test_remove_one1: count 5 (remove_one 5 [2;1;5;4;1]) = 0.
  Proof. reflexivity. Qed.
  Example test_remove_one2: count 5 (remove_one 5 [2;1;4;1]) = 0.
  Proof. reflexivity. Qed.
  Example test_remove_one3: count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
  Proof. reflexivity. Qed.
  Example test_remove_one4: count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
  Proof. reflexivity. Qed.

  Fixpoint remove_all (v:nat) (s:bag) : bag :=
    match s with
      | nil => nil
      | h :: t => if beq_nat v h then remove_all v t else h :: (remove_all v t)
    end.

  Example test_remove_all1: count 5 (remove_all 5 [2;1;5;4;1]) = 0.
  Proof. reflexivity. Qed.
  Example test_remove_all2: count 5 (remove_all 5 [2;1;4;1]) = 0.
  Proof. reflexivity. Qed.
  Example test_remove_all3: count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
  Proof. reflexivity. Qed.
  Example test_remove_all4: count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
  Proof. reflexivity. Qed.

  Fixpoint subset (s1:bag) (s2:bag) : bool :=
    match s1 with
      | nil => true
      | h :: t => andb (member h s2) (subset t (remove_one h s2))
    end.

  Example test_subset1: subset [1;2] [2;1;4;1] = true.
  Proof. reflexivity. Qed.
  Example test_subset2: subset [1;2;2] [2;1;4;1] = false.
  Proof. reflexivity. Qed.

  Theorem bag_theorem :
    forall (b : bag) (n : nat),
      count n (add n b) = (count n b) + 1.
  Proof.
    intros b n.
    simpl.
    rewrite <- beq_nat_refl. rewrite <- plus_1_l. rewrite -> plus_comm.
    reflexivity.
  Qed.

  Theorem nil_app : forall l : natlist,
                      [] ++ l = l.
  Proof.
    reflexivity.
  Qed.

  Theorem tl_length_pred : forall l : natlist,
                             pred (length l) = length (tl l).
  Proof.
    intros l. destruct l; reflexivity.
  Qed.

  Theorem app_assoc : forall l1 l2 l3 : natlist,
                        (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
  Proof.
    intros l1 l2 l3. induction l1 as [| n l1'].
    Case "l1 = nil". reflexivity.
    Case "l1 = cons n l1'".
      simpl. rewrite -> IHl1'. reflexivity.
  Qed.

  Theorem app_length : forall l1 l2 : natlist,
                         length (l1 ++ l2) = (length l1) + (length l2).
  Proof.
    intros l1 l2. induction l1 as [| n l1'].
    Case "l1 = nil". reflexivity.
    Case "l1 = cons".
      simpl. rewrite -> IHl1'. reflexivity.
  Qed.

  Fixpoint snoc (l:natlist) (v:nat) : natlist :=
    match l with
      | nil => [v]
      | h :: t => h :: (snoc t v)
    end.

  Fixpoint rev (l:natlist) : natlist :=
    match l with
        | nil => nil
        | h :: t => snoc (rev t) h
    end.

  Example test_rev1: rev [1;2;3] = [3;2;1].
  Proof. reflexivity. Qed.
  Example test_rev2: rev nil = nil.
  Proof. reflexivity. Qed.

  Theorem length_snoc : forall n : nat, forall l : natlist,
                          length (snoc l n) = S (length l).
  Proof.
    intros n l. induction l as [| n' l'].
    Case "l = nil". reflexivity.
    Case "l = cons n' l'".
      simpl. rewrite -> IHl'. reflexivity.
  Qed.

  Theorem rev_length : forall l : natlist,
                         length (rev l) = length l.
  Proof.
    intros l. induction l as [| n l'].
    Case "l = nil". reflexivity.
    Case "l = cons".
      simpl.
      rewrite -> length_snoc. rewrite -> IHl'.
      reflexivity.
  Qed.

  Theorem app_nil_end : forall l : natlist,
                          l ++ [] = l.
  Proof.
    intros l. induction l as [| n l'].
    Case "l = nil". reflexivity.
    Case "l = cons n l''".
      simpl.
      rewrite -> IHl'.
      reflexivity.
  Qed.

  Lemma snoc_cons_rev : forall n : nat, forall l : natlist,
                          rev (snoc l n) = n :: rev l.
  Proof.
    intros n l. induction l as [| n' l'].
    Case "l = nil". reflexivity.
    Case "l = n' :: l'".
      simpl.
      rewrite -> IHl'.
      reflexivity.
  Qed.

  Theorem rev_involutive : forall l : natlist,
                             rev (rev l) = l.
  Proof.
    intros l. induction l as [| n l'].
    Case "l = nil". reflexivity.
    Case "l = cons n l''".
      simpl.
      rewrite -> snoc_cons_rev. rewrite -> IHl'.
      reflexivity.
  Qed.

  Theorem app_assoc4:
    forall l1 l2 l3 l4 : natlist,
      l1 ++ (l2 ++ (l3 ++ l4)) = ((l1 ++ l2) ++ l3) ++ l4.
  Proof.
    intros l1 l2 l3 l4. induction l1 as [| n l1'].
    Case "l1 = nil".
      simpl.
      rewrite -> app_assoc.
      reflexivity.
    Case "l1 = n :: l1'".
      simpl.
      rewrite -> IHl1'.
      reflexivity.
  Qed.

  Theorem snoc_append : forall (l:natlist) (n:nat),
                          snoc l n = l ++ [n].
  Proof.
    intros l n. induction l as [| n' l'].
    Case "l = nil". reflexivity.
    Case "l = n' :: l'".
      simpl.
      rewrite -> IHl'.
      reflexivity.
  Qed.

  Theorem distr_rev : forall l1 l2 : natlist,
                        rev (l1 ++ l2) = (rev l2) ++ (rev l1).
  Proof.
    intros l1 l2. induction l1 as [| n l1'].
    Case "l1 = nil".
      simpl.
      rewrite -> app_nil_end.
      reflexivity.
    Case "l1 = n :: l1'".
      simpl.
      rewrite -> IHl1'.
      assert (H: snoc (rev l1') n = (rev l1') ++ [n]).
      SCase "Assertion".
        rewrite -> snoc_append.
        reflexivity.
      rewrite -> H.
      rewrite -> snoc_append. rewrite -> app_assoc.
      reflexivity.
  Qed.

  Lemma nonzeros_app : forall l1 l2 : natlist,
                         nonzeros (l1 ++ l2) = (nonzeros l1) ++ (nonzeros l2).
  Proof.
    intros l1 l2. induction l1 as [|n l1'].
    Case "l1 = nil". reflexivity.
    Case "l1 = n :: l1'".
      destruct n as [|n']; simpl; rewrite -> IHl1'; reflexivity.
  Qed.

  Fixpoint beq_natlist (l1 l2 : natlist) : bool :=
    match l1, l2 with
      | nil, nil => true
      | nil, _ => false
      | _, nil => false
      | h :: t, h' :: t' => if beq_nat h h'
                            then beq_natlist t t'
                            else false
    end.

  Example test_beq_natlist1 : beq_natlist nil nil = true.
  Proof. reflexivity. Qed.
  Example test_beq_natlist2 : beq_natlist [1;2;3] [1;2;3] = true.
  Proof. reflexivity. Qed.
  Example test_beq_natlist3 : beq_natlist [1;2;3] [1;2;4] = false.
  Proof. reflexivity. Qed.

  Theorem bew_natlist_refl : forall l : natlist,
                               true = beq_natlist l l.
  Proof.
    intros l. induction l as [|n l'].
    Case "l = nil". reflexivity.
    Case "l = n :: l'".
      simpl.
      rewrite <- beq_nat_refl.
      rewrite -> IHl'.
      reflexivity.
  Qed.

  Theorem count_member_nonzero : forall (s:bag),
                                   ble_nat 1 (count 1 (1 :: s)) = true.
  Proof.
    intros s. reflexivity.
  Qed.

  Theorem ble_n_Sn : forall n,
                       ble_nat n (S n) = true.
  Proof.
    intros n. induction n as [|n'].
    Case "0". reflexivity.
    Case "S n'".
      simpl.
      rewrite -> IHn'.
      reflexivity.
  Qed.

  Theorem bag_count_sum: forall (s1 s2:bag) (n:nat),
                           count n (sum s1 s2) = count n s1 + count n s2.
  Proof.
    intros s1 s2 n. induction s1 as [|n' s1'].
    Case "s1 = nil". reflexivity.
    Case "s1 = n' :: s1'".
      simpl.
      rewrite -> IHs1'.
      destruct (beq_nat n' n); reflexivity.
  Qed.

  Theorem rev_injective : forall (l1 l2 : natlist),
                            rev l1 = rev l2 -> l1 = l2.
  Proof.
    intros l1 l2 H.
    rewrite <- rev_involutive.
    rewrite <- H.
    rewrite -> rev_involutive.
    reflexivity.
  Qed.

  Inductive natoption : Type :=
  | Some : nat -> natoption
  | None : natoption.

  Fixpoint index (n:nat) (l:natlist) : natoption :=
    match l with
      | nil => None
      | a :: l' => match beq_nat n 0 with
                     | true => Some a
                     | false => index (pred n) l'
                   end
    end.

  Example test_index1 : index 0 [4;5;6;7] = Some 4.
  Proof. reflexivity. Qed.
  Example test_index2 : index 3 [4;5;6;7] = Some 7.
  Proof. reflexivity. Qed.
  Example test_index3 : index 10 [4;5;6;7] = None.
  Proof. reflexivity. Qed.

  Definition option_elim (d:nat) (o:natoption) : nat :=
    match o with
      | Some n' => n'
      | None => d
    end.

  Definition hd_opt (l:natlist) : natoption :=
    match l with
      | nil => None
      | h :: t => Some h
    end.

  Example test_hd_opt1 : hd_opt [] = None.
  Proof. reflexivity. Qed.
  Example test_hd_opt2 : hd_opt [1] = Some 1.
  Proof. reflexivity. Qed.
  Example test_hd_opt3 : hd_opt [5;6] = Some 5.
  Proof. reflexivity. Qed.

  Theorem option_elim_hd : forall (l:natlist) (default:nat),
                             hd default l = option_elim default (hd_opt l).
  Proof.
    intros l default. destruct l; reflexivity.
  Qed.

  Module Dictionary.

    Inductive dictionary : Type :=
    | empty : dictionary
    | record : nat -> nat -> dictionary -> dictionary.

    Definition insert (key value : nat) (d:dictionary) :
      dictionary := (record key value d).

    Fixpoint find (key:nat) (d:dictionary) : natoption :=
      match d with
        | empty => None
        | record k v d' => if (beq_nat key k)
                           then (Some v)
                           else (find key d')
      end.

    Theorem dictionary_invariant1' : forall (d:dictionary) (k v : nat),
                                       (find k (insert k v d)) = Some v.
    Proof.
      intros d k v.
      simpl. rewrite <- beq_nat_refl. reflexivity.
    Qed.

    Theorem dictioniary_invariant2' :
      forall (d:dictionary) (m n o : nat),
        beq_nat m n = false -> find m d = find m (insert n o d).
    Proof.
      intros d m n o H.
      simpl. rewrite -> H. reflexivity.
    Qed.

  End Dictionary.
End NatList.
