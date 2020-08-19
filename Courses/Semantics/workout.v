Require Import Arith Arith.EqNat.
Require Import Omega.
From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.

Lemma negbK (b : bool) : ~~ (~~ b) = b.
Proof.
    case: b.
    { trivial. }
    { trivial. } 
Qed.

Lemma leqn0 n : (n <= 0) = (n == 0).
Proof.
    by case: n => [|k].
    (* trivial. *)
    (* trivial. *)
Qed.

(* Print muln0. *)

Lemma muln_eq0 m n : (m * n == 0) = (m == 0) || (n == 0).
Proof.
    case: m => [|m]//.
    (* trivial.
    case: n => [|k]; last first.
    trivial. *)
    case: n => [|k]//.
    rewrite muln0.
    trivial.
Qed.

Lemma leqE m n : (m <= n) = (m - n == 0).
Proof.
    trivial.
Qed.

Lemma mulnBr n m p : n * (m - p) = n * m - n * p.
Proof.
    admit.
Admitted.


Lemma leq_mil2l m n1 n2 : (m * n1 <= m * n2) = (m == 0) || (n1 <= n2).
Proof.  
    rewrite !leqE.
    rewrite -mulnBr.
    rewrite muln_eq0.
    trivial.
Qed.

Theorem plus_id_example : forall n m : nat,
    n = m -> n + n = m + m.
Proof.
    intros n m.
    intros H.
    rewrite H.
    reflexivity.
Qed.

Theorem plus_id_exercise : forall n m o : nat,
    n = m -> m = o -> n + m = m + o.
Proof.
    intros n m o.
    intros H.
    intros HH.
    rewrite H.
    rewrite HH.
    reflexivity.

Qed.

Theorem plus_O_n : forall n : nat, 0 + n = n.
Proof.
  intros n. simpl. reflexivity. Qed.

Theorem mult_0_plus : forall n m : nat,
    (0 + n) * m = n * m.
Proof.
    intros n m.
    rewrite plus_O_n.
    reflexivity.
Qed.

Theorem mult_S_1 : forall n m : nat,
    m = S n ->
    m * (1 + n) = m * m.
Proof.
    intros n m H1.
    rewrite H1.
    reflexivity.
Qed.

Require Extraction. 
Extraction Language Haskell.
Extraction mult_0_plus.

Theorem plus_q_neq_0_firsttry : forall n : nat,
    (n + 1) =? 0 = false .
Proof.
    intros n.
    destruct n as [|n'] eqn:E.
    { reflexivity. }
    { reflexivity. } 
Qed.

Theorem negb_involutive : forall b : bool,
    negb (negb b) = b.
Proof.
    intros b.
    destruct b eqn:E.
    reflexivity.
    reflexivity.
Qed.

Theorem andb_commutative : forall b c, andb b c = andb c b.
Proof.
    intros [] [].
    - reflexivity.
    - reflexivity.
    - reflexivity.
    - reflexivity.
Qed.

Theorem  andb_true_elim2 : forall b c : bool,
    andb b c = true -> c = true.
Proof.
    intros [] [].
    trivial.
    trivial.
    trivial.
    trivial.
Qed.

Theorem zero_nbeq_plus_1 : forall n : nat,
    0 =? (n + 1) = false.
Proof.
    intros [].
    trivial.
    trivial.
Qed.


Module NatList.

Inductive natlist : Type :=
    | nil
    | cons (n : nat) (l : natlist).

Notation "x :: l" := (cons x l)
                     (at level 60, right associativity).
Notation "[ ]" := nil.
Notation "[ x ; .. ; y ]" := (cons x .. (cons y nil) ..).

Fixpoint repeat (n count : nat) : natlist :=
    match count with 
    | 0 => nil
    | S count' => n :: (repeat n count')
    end.
Fixpoint length (l : natlist) : nat := 
    match l with
    | nil => 0
    | h :: t => S (length t)
    end.
Compute length ([1;2;3]).

Fixpoint app (l_1 l_2 : natlist) : natlist :=
    match l_1 with
    | nil => l_2
    | h :: t => h :: (app t l_2)
    end.

Notation "x ++ y" := (app x y) 
                     (right associativity, at level 60).

Example test_app1: [1;2;3] ++ [4;5] = [1;2;3;4;5].
Proof. reflexivity. Qed.

Definition hd (default : nat) (l : natlist) : nat := 
    match l with
    | nil => default
    | h :: t => h
    end.

Definition tl (l : natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => t
    end.

Example test_hd1 : hd 0 [1;2;3] = 1.
Proof. reflexivity. Qed.

Example test_hd2 : hd 0 [] = 0.
Proof. reflexivity. Qed.

Example test_tl1 : tl [1;2;3] = [2;3].
Proof. reflexivity. Qed.

Fixpoint nonzeros (l : natlist) : natlist :=
    match l with
    | [] => []
    | 0 :: t => nonzeros t
    | x :: t => x :: nonzeros t
    end.

Example test_nonzeros:
    nonzeros [0;1;0;2;0;3] = [1;2;3].
Proof. reflexivity. Qed.

Fixpoint alternate (l1 l2 : natlist) : natlist :=
    match l1 with
    | [] => l2
    | x :: l1' =>
        match l2 with
        | [] => l1
        | y :: l2' => x :: y :: alternate l1' l2'
        end
    end. 

Example test_alternate1:        alternate [1;2;3] [4;5;6] = [1;4;2;5;3;6].
Proof. reflexivity.  Qed.
Example test_alternate2:        alternate [1] [4;5;6] = [1;4;5;6].
Proof. reflexivity.  Qed.
Example test_alternate3:        alternate [1;2;3] [4] = [1;4;2;3].
Proof. reflexivity.  Qed.
Example test_alternate4:        alternate [] [20;30] = [20;30].
Proof. reflexivity.  Qed.

Definition bag := natlist.

Fixpoint count (v : nat) (s : bag) : nat :=
    match s with
    | nil => 0
    | x :: x0 =>
        if beq_nat x v then 1 + count v x0 else count v x0
    end.

Definition sum : bag -> bag -> bag := app.

Example test_sum1:              count 1 (sum [1;2;3] [1;4;1]) = 3.
Proof. reflexivity.  Qed.

Definition member (v : nat) (s : bag) : bool :=
    negb (beq_nat (count v s) 0).

Fixpoint remove_one (v : nat) (s : bag) : bag :=
    match s with
    | nil => nil
    | x :: s' =>
        if beq_nat v x then s' else x :: remove_one v s'
    end.
Example test_remove_one1:         count 5 (remove_one 5 [2;1;5;4;1]) = 0.
Proof. reflexivity.  Qed.
Example test_remove_one2:         count 5 (remove_one 5 [2;1;4;1]) = 0.
Proof. reflexivity.  Qed.
Example test_remove_one3:         count 4 (remove_one 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity.  Qed.
Example test_remove_one4:         count 5 (remove_one 5 [2;1;5;4;5;1;4]) = 1.
Proof. reflexivity.  Qed.

Fixpoint remove_all (v : nat) (s : bag) : bag :=
    match s with
    | nil => nil
    | x :: s' =>
        if beq_nat v x
        then remove_all v s'
        else x :: remove_all v s'
    end.

Example test_remove_all1:          count 5 (remove_all 5 [2;1;5;4;1]) = 0.
Proof. reflexivity.  Qed.
Example test_remove_all2:          count 5 (remove_all 5 [2;1;4;1]) = 0.
Proof. reflexivity.  Qed.
Example test_remove_all3:          count 4 (remove_all 5 [2;1;4;5;1;4]) = 2.
Proof. reflexivity.  Qed.
Example test_remove_all4:          count 5 (remove_all 5 [2;1;5;4;5;1;4;5;1;4]) = 0.
Proof. reflexivity.  Qed.
Fixpoint subset (s1:bag) (s2:bag) : bool :=
  match s1 with
    | nil => true
    | cons x x0 =>
      if member x s2 then subset x0 (remove_one x s2) else false
  end.

Theorem nil_app : forall l : natlist,
    [] ++ l = l.
Proof.
    reflexivity.
Qed.

(* Print pred. *)

Theorem app_assoc : forall l1 l2 l3 : natlist,
    (l1 ++ l2) ++ l3 = l1 ++ (l2 ++ l3).
Proof.
    intros l1 l2 l3.
    induction l1 as [|n l1'].
    - reflexivity.
    - simpl. rewrite -> IHl1'. reflexivity.
Qed.

Theorem app_length : forall l1 l2 : natlist,
    length (l1 ++ l2) = (length l1) + (length l2).
Proof.
    intros l1 l2.
    induction l1 as [|n l1'].
    { reflexivity. }
    { simpl. rewrite -> IHl1'. reflexivity. }
Qed.

Fixpoint rev (l : natlist) : natlist :=
    match l with
    | nil => nil
    | h :: t => rev t ++ [h]
    end.

Example test_rev1 : rev [1;2;3] = [3;2;1].
Proof. reflexivity. Qed.

Theorem rev_lenght : forall l : natlist,
    length (rev l) = length l.
Proof.
    intros l.
    induction l as [| n l'].
    { simpl. reflexivity. }
    { simpl. rewrite -> app_length. simpl. rewrite -> IHl'. rewrite -> plus_comm. reflexivity. }
Qed.