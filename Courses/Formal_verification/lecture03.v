From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Section Logic.

(** more connectives *)

Inductive True : Prop :=
| I.

(** exercises *)
Definition t : True
:= I.   

Definition t_and_t : True /\ True
:=
conj I I.


Inductive False : Prop := .  (** <- notice the dot here *)


(** [not] is not a real connective, but like a macro, in Coq's terms it's a definition *)
Definition not (A : Prop) :=
  A -> False.

Notation "~ A" := (not A) : type_scope.


(** How to prove implications *)
Definition AimpliesA (A : Prop) :
  A -> A
:=
  fun proofA => proofA.

Definition AimpliesAandA (A : Prop) :
  A -> A /\ A
:=
  fun proofA => conj proofA proofA.

(** exercises *)
Definition A_implies_not_not_A (A : Prop) :
   A -> ~ ~ A
   (* A -> (A -> False) -> False *)
:=
    fun proofA => 
        fun f => f proofA
.

Fail Definition DNE (A : Prop) :
   ~ ~ A -> A
:= Admit.

Definition DNE' (A : Prop) :
  ~ ~ ~ A -> ~ A
  (* (((A -> False) -> False) -> False) -> A -> False *)
:=
    fun nnna a => 
        let
            nna := fun na => na a
        in nnna nna
.


(** Did you notice that double negation is a monad? *)


Definition exfalso_quodlibet (P : Prop) :
  False -> P
:=
  fun f =>
    match f with end.

Definition FalseImpliesFalse :
  False -> False
:= fun f => f.

End Logic.



Section FunctionalProgramming.

(** exercises *)
Definition const {A B : Type} (a : A) : B -> A
:=
    fun b => a
.


Definition flip {A B C : Type} (f : A -> B -> C) : B -> A -> C
:=
    fun a b => f b a
.

Definition curry {A B C : Type} (f : A * B -> C) : A -> B -> C
:=
    fun a b => f (pair a b)
.

Definition uncurry {A B C : Type} (f : A -> B -> C) : A * B -> C
:=
    fun ab => 
        match ab with
        | pair a b => f a b
        end
.

End FunctionalProgramming.

Arguments const {A B} a _ /.
Arguments flip {A B C} f b a /.
Arguments curry {A B C} f a b /.
Arguments uncurry {A B C} f _ /.


Section LogicAgain.

(** exercises *)
Definition TODO_better_name (A B : Prop) :
  A -> B -> A
:= const.

Definition contraposition (A B : Prop) :
  (A -> ~ B) -> (B -> ~ A)
:=
    fun f => flip f
.

Fail Definition LEM (A : Prop) :
   A \/ ~A
:=
    admit
.

Definition LEMisNotFalse (A : Prop) :
  ~ ~ (A \/ ~A)
  (* ( (or A (A -> False)) -> False) -> False *)
:=
    fun nl =>
        let l := or_intror( fun a => nl (or_introl a) )
    in 
    nl l
.

End LogicAgain.



Module MyNamespace.
Section Propositional_Equality.

(** parameters vs indices *)
Inductive eq (A : Type)
(**           ^^^^^^^^  parameter *)
             (a : A) :
(**           ^^^^^     parameter *)
              A -> Prop :=
(**           ^          index *)
| eq_refl : eq a a.

Notation "a = b" := (eq a b) : type_scope.


Definition eq_reflexive A (x : A) :
  x = x
:=
    eq_refl x
.

(* dependent pattern matching *)
Definition eq_sym A (x y : A) :
  x = y -> y = x
  (* eq x y -> eq y x *)
:=
    fun arg => 
    match arg with
    | eq_refl => eq_refl x
    end
.

Definition eq_trans A (x y z : A) :
  x = y -> y = z -> x = z
  (* eq x y -> eq y z -> eq x z *)
:=
    fun arg1 => 
        fun arg2 => 
            match arg1 with
            | eq_refl => 
                match arg2 with
                | eq_refl => arg1
                end
            end
.

End Propositional_Equality.
End MyNamespace.