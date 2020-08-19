From mathcomp Require Import ssreflect ssrfun ssrbool ssrnat.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** Prove the following "lemmas" by providing explicit terms and answer some questions *)

(** * IMPORTANT! DO NOT USE TACTICS TO SOLVE THESE EXERCISES *)

(** Try to solve the exercises first without looking at the hints *)



(** * Exercise 1 *)
Section BooleanLogic.

(** Exercise 1a *)

(** Convince yourself [bool_eq] is a function that decides equality on type [bool],
    write all the four unit tests if you need to. *)
Definition eqb (b : bool) : bool -> bool :=
  if b then id else negb.

Compute eqb true true.
Compute eqb false false.
Compute eqb true false.
Compute eqb false true.

Notation "b == c" := (eqb b c) (no associativity, at level 70).

Definition iff_is_if_and_only_if :
  forall a b : bool, (a ==> b) && (b ==> a) = (a == b)
:=
  fun (a b : bool) =>
    match a with
    | true => match b with
              | true => erefl true
              | false => erefl false
              end
    | false => match b with
              | true => erefl false
              | false => erefl true
              end
      end
.


(** Hint 1: use [Locate "==>".] to see what this notation means.
    Hint 2: it means [implb b c], use [Print implb.] to see [implb] works.
    Hint 3: think of how you would prove this in classical logic
            ([==>] stands for classical implication and [==] means classical equivalence)
            and apply this intuition here.
 *)


(** Exercise 1b: double negation elimination *)
Definition negbNE :
  forall b : bool, ~~ ~~ b = true -> b = true
:= 
  fun b =>
    match b with
    | true => fun nnb => erefl
    | false =>  fun nnb => match nnb with
                | erefl => 42
                end
    end 
.

(** Hint: [~~] is a separate token, find out it's meaning. *)

(** Have you noticed that in the decidable fragment of logic we are free to remove double negation? *)

End BooleanLogic.



(** * Exercise 2 *)

Section ExtensionalEqualityAndComposition.


Variables A B C D : Type.

(** Exercise 2a *)
(** [\o] is a notation for function composition in MathComp, prove that it's associative *)

Definition compA (f : A -> B) (g : B -> C) (h : C -> D) :
  (h \o g) \o f = h \o (g \o f)
:=
  erefl ((h \o g) \o f)
.


(** [=1] stands for extensional equality on unary functions,
    i.e. [f =1 g] means [forall x, f x = g x].
    This means it's an equivalence relation, i.e. it's reflexive, symmetric and transitive.
    Let us prove a number of facts about [=1]. *)


(** DO NOT USE LEMMAS OR DEFINITIONS IN THE PROOFS IN THIS SECTION! Do all the pattern-matching by hand *)

(** Exercise 2b: Reflexivity *)
Definition eqext_refl :
  forall (f : A -> B), f =1 f
:=
  fun f x => erefl (f x)
.

Print "=1".

(** Exercise 2c: Symmetry *)
Definition eqext_sym :
  forall (f g : A -> B), f =1 g -> g =1 f
:=
  fun f g fg a => 
    match (fg a) with
    | erefl => erefl (f a)
    end
.

(** Exercise 2d: Transitivity *)
Definition eqext_trans :
  forall (f g h : A -> B), f =1 g -> g =1 h -> f =1 h
:=
  fun f g h fg gh a =>
    match gh a with
    | erefl => fg a
    end
.


(** Exercise 2e: left congruence *)
Definition eq_compl :
  forall (f g : A -> B) (h : B -> C),
    f =1 g -> h \o f =1 h \o g
:=
  fun f g h fg x =>
    match fg x 
    in (_ = g')
    return (h (f x) = h g')
    with
    | erefl => erefl
    end
.

(** Exercise 2f: right congruence *)
Definition eq_compr :
  forall (f g : B -> C) (h : A -> B),
    f =1 g -> f \o h =1 g \o h
:=
  fun f g h fg x =>
    match fg (h x)
    with
    | erefl => erefl
    end
.

End ExtensionalEqualityAndComposition.



(** * Exercise 3 *)
Section Quantifiers.

Variable T : Type.
Variable P Q : T -> Prop.

(** Exercise 3a *)
Definition forall_conj_comm :
  (forall x, P x /\ Q x) <-> (forall x, Q x /\ P x)
:=
  conj
  (fun pq x =>
  match pq x with
  | conj p q => conj q p
  end)
  (fun qp x =>
  match qp x with
  | conj q p => conj p q
  end)
.


(** Exercise 3b *)
Definition forall_disj_comm :
  (forall x, P x \/ Q x) <-> (forall x, Q x \/ P x)
:=
  conj 
  (fun pq x =>
    match pq x with
    | or_introl px => or_intror px
    | or_intror qx => or_introl qx
    end
  )
  (fun qp x =>
    match qp x with
    | or_introl qx => or_intror qx
    | or_intror px => or_introl px
    end
  )
.

(** Exercise 3c *)
Definition exists_introduction :
  forall (x : T), P x -> (exists (x : T), P x)
:=
  fun x px => @ex_intro T P x px
.

End Quantifiers.



(** * Optional exercises, feel free to skip them *)

Fixpoint divn (n m : nat) : nat :=
  let fix
  divmod n m r s :=  match n with
    | 0 => (r, s)
    | S n' => match s with
                | 0 => divmod n' m (S r) m
                | S s' => divmod n' m r s'
              end
  end
  in match m with
  | 0    => m
  | S m' => fst (divmod n m' 0 m')
  end 
.

(* Unit tests: *)
Check erefl : divn 0 0 = 0.
Check erefl : divn 1 0 = 0.
Check erefl : divn 0 3 = 0.
Check erefl : divn 1 3 = 0.
Check erefl : divn 2 3 = 0.
Check erefl : divn 3 3 = 1.
Check erefl : divn 8 3 = 2.
Check erefl : divn 42 0 = 0.
Check erefl : divn 42 1 = 42.
Check erefl : divn 42 2 = 21.
Check erefl : divn 42 3 = 14.
Check erefl : divn 42 4 = 10.
Check erefl : divn 42 30 = 1.


(** Exercise: the dual Frobenius rule *)
Definition LEM :=
  forall P : Prop, P \/ ~ P.

Definition Frobenius2 :=
  forall (A : Type) (P : A -> Prop) (Q : Prop),
    (forall x, Q \/ P x) <-> (Q \/ forall x, P x).

Definition lem_iff_Frobenius2 :
  LEM <-> Frobenius2
:=
.