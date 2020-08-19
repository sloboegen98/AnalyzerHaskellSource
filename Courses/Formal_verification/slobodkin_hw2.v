From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** Ex. 1: implement a function [div2] of type [nat -> nat]
           which divides the input number by 2.
           Do not use any standard functions to implement this.
           Add some unit tests. *)

Fixpoint div2_helper (res n : nat) : nat :=
	match n with
		| O       => res
		| S O     => res
		| S (S k) => div2_helper (S res) k
	end.

Definition div2 (n : nat) : nat := div2_helper O n.

Compute div2 (S (S O)).
Compute div2 (S (S (S (S (S O))))).
Compute div2 (S (S (S (S O)))).
Compute div2 (S O).


(** Ex. 2: implement multiplication on natural numbers
           using [applyn] from lecture 2.
           Do not use recursion! (no [fix], [Fixpoint] or similar mechanisms).
           Write unit tests. *)

Definition applyn :=
	fun (f : nat -> nat) =>
		fix rec n x {struct n} : nat :=
			if n is S n' 
			then f (rec n' x)
			else x.

Fixpoint addn (n m : nat) {struct n} : nat :=
      if n is S n' then S (addn n' m)
      else m.

Definition muln (n m : nat) : nat := (applyn (addn n) m) O.

Compute muln 2 10.
Compute muln 4 5.
Compute muln 0 2.
Compute muln 1 10.
Compute muln 5 6.
Compute muln 6 5.


(** DO NOT USE TACTICS TO SOLVE THE FOLLOWING EXERCISES! *)

(** Ex. 1: implement a function reassociating the components of a triple *)
Definition tripleA (A B C : Prop) :
  (A * B) * C -> A * (B * C)
	:= fun tr =>
		match tr with
			| pair (pair a b) c => pair a (pair b c)
		end.


(** Ex. 2: prove that conjunction is associative  *)
Definition andA (A B C : Prop) :
  (A /\ B) /\ C -> A /\ (B /\ C)
:=  fun term =>
		match term with
			| conj (conj a b) c => conj a (conj b c)
		end.


(** Ex. 3: implement constructive disjunction (called the type [or])
           as explained during the seminar.
           Hint: we have mentioned that contructive disjunction corresponds to
           the [sum] type.
		   Introduce notation [\/] to stand for [or] *)

Inductive and (A B : Prop) : Prop :=
	| conj of A & B.
		 
Notation "A /\ B" := (and A B) : type_scope.

Inductive or (A B : Prop) : Prop := 
	| or_l of A
	| or_r of B.

Notation "A \/ B" := (or A B) : type_scope.

Arguments or_l [A B] a, [A] B a.
Arguments or_r [A B] b, A [B] b.


(** Ex. 4: Prove that conjunction distributes over disjunction: *)
Definition conj_disjD (A B C : Prop) :
  A /\ (B \/ C) -> A /\ B \/ A /\ C
	:= fun term =>
		match term with 
			| conj a (or_l b) => or_l (conj a b)
			| conj a (or_r c) => or_r (conj a c)
		end.


(** Ex. 5: Prove that disjunction distributes over conjunction: *)
Definition disj_conjD (A B C : Prop) :
  A \/ (B /\ C) -> (A \/ B) /\ (A \/ C)
	:= fun term =>
		match term with
			| or_l a => conj (or_l a) (or_l a)
			| or_r (conj b c) => conj (or_r b) (or_r c)
		end. 