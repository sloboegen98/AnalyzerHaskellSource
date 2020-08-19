From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.

Module Propositional_Equality.


(* dependent pattern matching *)
Definition eq_sym A (x y : A) :
  x = y -> y = x
  :=     
  fun xy => 
  match xy with
  | erefl => erefl x
  end
.

(* Print  eq_sym. *)

Definition eq_trans A (x y z : A) :
  x = y -> y = z -> x = z
:= 
    fun xy =>
    match xy with
    | erefl => id 
    end.

(** This does not work *)
Fail Definition eq_trans' A (x y z : A) :
  x = y -> y = z -> x = z
:= 
fun pf_xy : x = y =>
  fun pf_yz : y = z =>
    match pf_xy with
    | erefl => pf_yz
    end.
(* The term "pf_yz" has type "y = z" while it is expected to have type "x = z". *)

(** Why? Let's go back a bit *)

(**
General form of pattern matching construction:
[match expr as T in depType return exprR].

- [as T] is needed when we are matching on complex expressions, not just variables
- [in depType] lets us bind _indices_ of the type of the input expression [expr]
- [return exprR] denotes the dependent type of the expression
*)


(** Notice that we did not use the more general form of [match]-expression
    because Coq's heuristics can sometimes infer the missing bits.
    Let us redo the previous lemmas and fill in them manually. *)

Module AnnotatedMatch.
Definition eq_sym A (x y : A) :
  x = y -> y = x
  := 
  fun xy =>
  match xy in (_ = y)
    return (y = x) with
    | erefl => erefl 
  end.

Definition eq_trans A (x y z : A) :
  x = y -> y = z -> x = z
:= 
    fun (xy : x = y) (yz : y = z) =>
    match yz in (_ = z)
        return (x = z) with
    | erefl => xy
    end.

(** this is where our previous mental model breaks down *)
Fail Definition eq_trans' A (x y z : A) :
  x = y -> y = z -> x = z
:= 
fun pf_xy : x = y =>
  fun pf_yz : y = z =>
    match
      pf_xy in (_ = y)
      return (x = z)
    with
    | erefl =>
      pf_yz
    end.  (** the type of pf_yz is fixed and dependent pattern mathching over pf_xy
                 does _not_ change it to [x = z] *)

(** let us fix it now *)
(* Definition eq_trans' A (x y z : A) :
  x = y -> y = z -> x = z
:=
  . *)

End AnnotatedMatch.

(** * Injectivity of constructors *)

Definition succ_inj (n m : nat) :
  S n = S m -> n = m
:=
  fun snsm : S n = S m =>
    match snsm in (_ = sm)
          return (n = sm.-1)
    with
    | erefl => erefl n
    end.


(** * Disjointness of constructors *)

Definition false_eq_true_implies_False :
  false = true -> False
:=
fun     eq :  false = true =>
match eq in (_    = b)
         return (if b then False else True)
with
| erefl => I
end.

(** * Convoy pattern *)
(* Definition neq_sym A (x y : A) :
  x <> y -> y <> x
:=

. *)


(** * Exercises *)

(** exercise: *)
Definition f_congr {A B} (f : A -> B) (x y : A) :
  x = y  ->  f x = f y
  (* eq x -> eq (f x) *)
:=
    fun xy =>
        match xy in (_ = y)
            return (f x = f y)  with
        | erefl => erefl (f x)
        end
.

(* exercise: *)
Definition f_congr' A B (f g : A -> B) (x y : A) :
  f = g  ->  x = y  ->  f x = g y
:=
    fun (fg : f = g) (xy : x = y) =>
        match fg in (_ = g)
            return (f _ = g _) with
        | erefl =>   
            match xy in (_ = y)
                return (_ x = _ y) with
                | erefl => erefl (f x)
            end
        end
.


(* exercise *)
Definition pair_inj A B (a1 a2 : A) (b1 b2 : B) :
  (a1, b1) = (a2, b2) -> (a1 = a2) /\ (b1 = b2)
:=
    fun eqp =>
        match eqp in (_ = p2)
            return (match p2 with
                    | (a2, b2) => (a1 = a2) /\ (b1 = b2) 
                   end) with
        | erefl => match (a1, b1) with
                    | (a2, b2) => conj erefl erefl
                    end
        end
.


(* optional exercise, feel free to skip this if you don't have prev. experience with Coq  *)
(*
Definition unit_neq_bool:
  unit <> bool
:=
 *)


End Propositional_Equality.




(*** Universal
     quantifier *)

(** * Motivation *)

(** Suppose we wrote two functions: a simple (a.k.a. gold) implementation
    and its optimized version.
    How do we go about specifying their equivalence?
 *)

Section Motivation.
Variables A B : Type.

Variables fgold fopt : A -> B.

Lemma fopt_equiv_fgold :
  forall x : A, fgold x = fopt x.
Abort.

End Motivation.


(** * Dependently typed functions *)

(** ** Dependently typed predecessor function *)

Definition Pred n := if n is S n' then nat else unit.

(** the value of [unit] type plays the role of a placeholder *)
Print unit.

Definition predn_dep : forall n, Pred n :=
  fun n => if n is S n' then n' else tt.

Check erefl : predn_dep 7 = 6.
Fail Check erefl : predn_dep 0 = 0.
Check erefl : predn_dep 0 = tt.
Check predn_dep 0 : unit.
Check erefl : Pred 0 = unit.
Check predn_dep 7 : nat.


(** ** Annotations for dependent pattern matching *)

(** Reminder: Type inference for dependent types is undecidable *)
Fail Check (fun n => if n is S n' then n' else tt).

Check (fun n =>
  if n is S n' as n0 return Pred n0 then n' else tt).


(** * Functional type is just a notation
      for a special case of [forall]  *)

Locate "->".

Check predn : nat -> nat.
Check predn : forall x : nat, nat.
Check predn : forall x : nat, (fun _ => nat) x.


(** * Usage of [forall] in standalone expressions *)

(* courtesy of Mathcomp book *)
Section StandardPredicates.
Variable T : Type.
Implicit Types (op add : T -> T -> T).

Definition associative op :=
  forall x y z, op x (op y z) = op (op x y) z.

Definition left_distributive op add :=
  forall x y z, op (add x y) z = add (op x z) (op y z).

Definition left_id e op :=
  forall x, op e x = x.

End StandardPredicates.



(*** Existential
     quantifier *)
Module MyExistential.

Inductive ex_my (A : Type) (P : A -> Prop) : Prop :=
| ex_intro_my (x : A) (proof : P x).

(** Simplified notation *)
Notation "’exists’ x : A , p" := (ex (fun x : A => p))
                                   (at level 200, right associativity).

(** Full-blown notation: multiple binders *)
Notation "'exists' x .. y , p" :=
  (ex_my (fun x => .. (ex_my (fun y => p)) ..))
  (at level 200, x binder, right associativity,
   format "'[' 'exists'  '/  ' x  ..  y ,  '/  ' p ']'")
  : type_scope.
End MyExistential.


Lemma exists_not_forall A (P : A -> Prop) :
  (exists x, P x) -> ~ (forall x, ~ P x).
Proof.
  case=> x px.
  move=>all.
  
Qed.


Definition exists_not_forall A (P : A -> Prop) :
  (exists x, P x) -> ~ (forall x, ~ P x)
:=
.

(** Currying for dependent pairs *)
Definition curry_dep A (P : A -> Prop) Q :
  ((exists x, P x) -> Q) -> (forall x, P x -> Q)
:=
  .


