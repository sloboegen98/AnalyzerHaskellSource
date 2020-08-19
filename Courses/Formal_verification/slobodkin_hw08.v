From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** Give two proofs of the following lemma:
    1. using [apply/view1/view2] idiom
    2. using [exact] tactic and [sameP] view lemma
*)
Lemma size_eq0 (T : eqType) (s : seq T) :
  (size s == 0) = (s == [::]).
Proof.
    apply/idP.
    case s => //=.
(** First proof *)
Restart.
(** Second proof *)
Admitted.




(** * Odd and even numbers *)

Section OddAndEven.

(** The goal of this exercise is to build a system of canonical structures
    so that the following statement about some properties of
    odd natural numbers can be proved with a couple of simple rewrites:

    Example test_odd (n : odd_nat) :
      ~~ (odd 6) && odd (n * 3).
    Proof. by rewrite oddP evenP. Qed.

    See the definitions of [odd_nat], [oddP], and [evenP] below.
    If you do everything the right way the example at the end of the section will work.
    In other words, the goal of this exercise is not to prove a statement,
    but rather make the given proof work.
    Please, DO NOT CHANGE the proof (I can assure you it works if the right canonical structures are given)
 *)


(** Let us define a structure defining the notion of odd numbers *)
Structure odd_nat := Odd {
  oval : nat;            (** [oval] is a natural number *)
  oprop : odd oval       (** [oprop] is the proof it is odd *)
}.

(** Example: [42 - 1] is an odd number *)

Definition o41 : odd_nat := @Odd 41 isT.

(** One issue here is that we cannot, for instance, add two odd naturals: *)
Fail Check o41 + o41.

(** Let's declare [oval] a coercion to work with terms of type [odd_nat]
    as if those were just regular naturals.
 *)
Coercion oval : odd_nat >-> nat.

Check o41 + o41.    (** Notice the result type is [nat] here: to use [odd_nat] as [nat] we forget the
                        extra information about oddity *)

(** Prove the main property of [odd_nat] *)
Lemma oddP {n : odd_nat} : odd n.
Proof.
  apply: oprop.
Qed.

(** Let us do the analogous thing for the even numbers *)
Structure even_nat := Even {
  eval :> nat;
  eprop : ~~ (odd eval)
}.

(* Prove the main property of [even_nat] *)
Lemma evenP {n : even_nat} : ~~ (odd n).
Proof.
  apply: eprop.
Qed.


(** Now we have all the definitions we referred to in the problem definition.  *)

(** The objective is to make it work: knowing that
    [n] is [odd] Coq should infer that [n * 3]
    is also [odd], and that [6] is even *)
Example test_odd (n : odd_nat) : ~~ (odd 6) && odd (n * 3).
Proof. Fail by rewrite oddP evenP. Abort.

(** But Coq cannot infer it without any hints.
    The goal to provide the necessary hints in the form of canonical structure instances *)

(** Let's start by telling Coq that 0 is even *)
Canonical even_0 : even_nat := @Even 0 isT.
(* WRITE_YOUR_PROOF_TERM_HERE. *)

(** helper lemma *)
Lemma oddS n : ~~ (odd n) -> odd n.+1.
Proof.
  by [].
Qed.

(** helper lemma *)
Lemma evenS n : (odd n) -> ~~ (odd n.+1).
Proof.
  by move=> oddn; apply/negPn.
Qed.

(** Here we teach Coq that if [m] is even,
    then [m.+1] is [odd] *)
Canonical odd_even (m : even_nat) : odd_nat :=
  @Odd m.+1 (oddS (eprop m)).

(** Implement the dual, teach Coq that if [m]
    is [odd] then [m.+1] is [even] *)
Canonical even_odd (m : odd_nat) : even_nat :=
  @Even m.+1 (evenS (oprop m)). 

(** Now let's deal with multiplication: DO NOT USE [case] tactic or the square brackets to
    destruct [n] or [m] *)
Lemma odd_mulP {n m : odd_nat} : odd (n * m).
Proof.
  rewrite odd_mul.
  apply/ andP.
  split; apply oprop.
Qed.
(** (!) do not break up [n] o [m] *)

(** Teach Coq that [*] preserves being [odd] *)
Canonical oddmul_Odd (n m : odd_nat) : odd_nat :=
  @Odd (n * m) (odd_mulP).

(** If the following proof works it means you did everything right: *)
Example test_odd (n : odd_nat) :
  ~~ (odd 6) && odd (n * 3).
Proof. by rewrite oddP evenP. Qed.

End OddAndEven.


(** An optional exercise with a short and a bit tricky one-line solution (less than 70 characters): *)
Lemma triple_compb (f : bool -> bool) :
  f \o f \o f =1 f.
Proof.
Admitted.
(** Hint: use [case <identifier>: <term>] tactic
          to pattern match on [<term>] and keep the result
          as an equation <identifier> in the context.
          E.g. [case E: b] where [b : bool] creates two subgoals with two equations
          in the context: [E = true] and [E = false] corresponingly.
 *)



(** Optional exercises *)
Section EckmannHilton.
(** Here is an explanation for this section:
    https://en.wikipedia.org/wiki/Eckmann–Hilton_argument
    Hint: you can find informal proofs in that wiki page,
          use it as a source of inspiration if you get stuck.
 *)

Context {X : Type}.
Variables f1 f2 : X -> X -> X.

Variable e1 : X.
Hypothesis U1 : left_id e1 f1 * right_id e1 f1.

Variables e2 : X.
Hypothesis U2 : left_id e2 f2 * right_id e2 f2.

Hypothesis I : interchange f1 f2.

Lemma x_is_f1xe1 (x : X) :
  x = f1 x e1.
Proof.
  by rewrite U1.
Qed.

Lemma f1_eq_f1f2f2 (x y : X) : 
  f1 x y = f1 (f2 x e2) (f2 e2 y).
Proof.
  by rewrite !U2.
Qed.

Lemma units_same :
  e1 = e2.
Proof.
  rewrite (x_is_f1xe1 e1).
  rewrite f1_eq_f1f2f2.
  rewrite I.
  rewrite !U1.
  by rewrite U2.
Qed.

Lemma operations_equal :
  f1 =2 f2.
Proof.
  move=> x y.
  rewrite f1_eq_f1f2f2.
  rewrite I.
  rewrite -units_same.
  by rewrite !U1.
Qed.  

Lemma I1 : interchange f1 f1.
Proof.
  rewrite/ interchange.
  move=> a b c d.
  rewrite operations_equal.
  rewrite -I.
  rewrite -operations_equal.
  by rewrite -operations_equal.
Qed.

Lemma rewrite_f2_x_y_rl (x y : X) :
  f2 x y = f2 (f1 e1 x) (f1 y e1).
Proof.
  by rewrite !U1.
Qed.

Lemma operations_comm :
  commutative f1.
Proof.
  rewrite/commutative.
  move=> x y.
  rewrite f1_eq_f1f2f2.
  rewrite I.
  rewrite -!units_same.
  rewrite !U1.
  rewrite rewrite_f2_x_y_rl.
  rewrite -I.
  rewrite !units_same.
  by rewrite !U2.
Qed.

Lemma helper_assoc (x y z : X) :
  f1 x (f1 y z) = f1 (f1 x e1) (f1 y z).
Proof.
  by rewrite U1.
Qed.

Lemma operations_assoc :
  associative f1.
Proof.
  rewrite/associative.
  move=> x y z.
  rewrite helper_assoc.
  rewrite operations_equal.
  rewrite -I.
  rewrite units_same.
  by rewrite -operations_equal U2.
Qed.

End EckmannHilton.