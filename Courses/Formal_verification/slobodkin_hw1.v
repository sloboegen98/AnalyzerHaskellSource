From mathcomp Require Import ssreflect.

Module My.

(** We introduce these definitions inside a new module
    to avoid name clashes with the standard library later *)

(** Some definitions we introduced during our lecture *)
Inductive bool : Type :=
| true
| false.

Definition negb :=
  fun (b : bool) =>
    match b with
    | true => false
    | false => true
    end.

(** * Exercise 0 : fun with functions *)

(** 0a. Define an anonymous (lambda) function that takes
        - a function [f] of type [bool -> bool] and
        - an argument [b] of type [bool]
        and applies [f] twice to [b].
        Check its type and try using it on the function [negb] and
        some boolean terms of your liking, e.g: *)

Check (fun (f : bool -> bool) (b : bool) => f (f b)).
Compute (fun (f : bool -> bool) (b : bool) => f (f b)) negb true.


(** * Exercise 1 : boolean functions *)

(** 1a. Define [orb] function implementing boolean disjunction *)

Definition orb (b c : bool) : bool := 
	match b with
	| true => true
	| false => c
	end.


(** 1b. Test [orb] _thoroughly_ using the command [Compute].
        How many cases should you consider? *)

Compute orb true false.
Compute orb false true.
Compute orb false false.


(** 1c. Define [xorb] function implementing _exclusive_ boolean disjunction
        Try to come up with more than one definition (try to make it interesting
        and don't just swap the variables) *)

Definition andb (b c : bool) : bool :=
	match b with
	| false => false
	| true => c
	end.

Definition xorb (b c : bool) : bool := orb (andb b (negb c)) (andb (negb b) c).

(** 1d. Test [xorb] thoroughly using the command [Compute]. *)

Compute xorb true true.
Compute xorb true false.
Compute xorb false true.
Compute xorb false false.

(** 1d. Define [eqb] function implementing equality on booleans, i.e.
        [eqb b c] must return [true] if and only iff [b] is equal to [c] *)

Definition eqb (b c : bool) : bool := orb (andb b c) (andb (negb b) (negb c)).

(** 1d. Test [eqb] thoroughly using the command [Compute]. *)

Compute eqb true true.
Compute eqb false false.
Compute eqb true false.
Compute eqb false true.


(** * Exercise 2 : arithmetic *)

Inductive nat : Type :=
| O
| S of nat.


(** 2a. Define an [inc2] function of type [nat -> nat] which takes
        a natural number and increments it by 2 *)

Definition inc2 (n : nat) : nat := S (S n).

(** 2b. Write some unit tests for [inc2] *)

Compute inc2 O.
Compute inc2 (S (S O)).
Compute inc2 (S (S (S O))).


(** 2c. Define an [dec2] function of type [nat -> nat] which takes
        a natural number and decrements it by 2, e.g.
        for the number [5] it must return [3]. *)

Definition dec2 (n : nat) : nat := 
	match n with
	| O       => O
	| S O     => O
	| S (S n) => n
	end.  

(** 2b. Write some unit tests for [dec2] *)

Compute dec2 O.
Compute dec2 (S O).
Compute dec2 (S (S O)).
Compute dec2 (S (S (S O))).
Compute dec2 (S (S (S (S O)))).


(** 2c. Define an [sub] function of type [nat -> nat -> nat] which takes
        two natural numbers [x] and [y] and returns the result of
        subtracting [y] from [x]. E.g. [sub 5 3] returns [2]. *)

(* if x < y then x - y := 0 *)

Fixpoint subn (m n : nat) : nat := 
	match n with 
	| O    => m
	| S n' => 
		match m with
		| O => O
		| S m' => subn m' n'
		end
	end.

(** 2d. Write some unit tests for [subn] *)

Compute subn (S (S (S (S (S O))))) (S (S O)).
Compute subn (S O) (S O).
Compute subn (S (S (S O))) (S O).
Compute subn (S (S (S O))) O.
Compute subn (S O) (S (S O)).

(** ---------------------------------------------------------------------------- *)

(** Extra: implement an equality comparison function [eqn] on natural numbers
           of type [nat -> nat -> bool]. It returns true if and only if
		   the input numbers a equal. *)
		   
Definition eqn (n m : nat) : bool :=
	match (subn n m) with
	| S n' => false	
	| O    => match (subn m n) with 
		| S n' => false
		| O => true
		end
	end.

Compute eqn O O.
Compute eqn (S O) O.
Compute eqn (S O) (S O).
Compute eqn (S (S O)) (S (S (S O))).
Compute eqn (S (S O)) (S (S O)).

Fixpoint eqn' (n m : nat) : bool := 
	match n with 
	| O => match m with
		   | O    => true
		   | S m' => false
		   end
	| S n' => match m with
			  | O 	 => false
			  | S m' => eqn' n' m'
			  end
	end.  		

Compute eqn' O O.
Compute eqn' (S O) O.
Compute eqn' (S O) (S O).
Compute eqn' (S (S O)) (S (S (S O))).
Compute eqn' (S (S O)) (S (S O)).