From mathcomp Require Import ssreflect ssrbool ssrnat.

(** Prove the following "lemmas" by providing explicit terms and answer some questions *)

(** * IMPORTANT! DO NOT USE TACTICS TO SOLVE THESE EXERCISES *)

(** Try to solve the exercises first without looking at the hints *)

Section IntLogic.

Variables A B C : Prop.


(** Exercise 1 *)
Definition notTrue_iff_False : (~ True) <-> False
(* ((True -> False) -> False) /\ (False -> True -> False) *)
:=
    conj (fun f => f I) (fun x y => x).

(* Hint 1: use [Locate "<->".] and [Print iff.] commands to understand better the type above. *)
(* Hint 2: If you are experiencing an error like the following one
           "Found a matching with no clauses on a term unknown to have an empty inductive type."
           try adding explicit type annotations to functional parameters or
           use [match <term> in <type> with ... end] instead of [match <term> with ... end]
 *)



(** Exercise 2: prove that implication is transitive. What does this logical lemma correspond to
                in functional programming? *)
(* function composition *)
Definition imp_trans : (A -> B) -> (B -> C) -> (A -> C)
:=
    fun f => fun g => fun arg => g (f arg)
.

(** Exercise 3: double negation elimination works for [False] *)
Definition dne_False : ~ ~ False -> False
(* ((False -> False) -> False) -> False *)
:=
    fun f => f id
.


(** Exercise 4: double negation elimination works for [True] too.
                Give a solution using one of the standard functions we saw previously (you will need to
                copy its definition in this file). *)

Definition const {A B : Type} (a : A) : B -> A
:=
    fun b => a
.
                

Definition dne_True : ~ ~ True -> True
(* ((True -> False) -> False) -> True *)
:=
    const I
.


(** Exercise 5: Peirce's law (look it up on the Internet) is equivalent to
                and Double Negation Elimination, so it does not hold in general,
                but we can prove its weak form. *)
Definition weak_Peirce : ((((A -> B) -> A) -> A) -> B) -> B
:=
    fun abaab =>
        let
            abaa : ((A -> B) -> A) -> A := fun aba =>
                let
                    ab : A -> B := fun a => let
                        b := abaab (fun arg => a)
                    in b
                in aba ab
        in abaab abaa
.
(* Hint 1a: use let-in expression to break the proof into pieces and solve them more independently *)
(* Hint 1b: annotate the identifiers of let-expressions with types: [let x : <type> := ... in ...] *)

End IntLogic.

Section EqualityPart1.

Definition eq1 : true = (true && true)
:=
eq_refl true
.

Definition eq2 : 42 = (if true then 21 + 21 else 239)
:=
eq_refl 42
.

End EqualityPart1.
