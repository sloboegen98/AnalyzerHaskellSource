From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(*** Boolean reflection,
     continued *)

Section BooleanReflection.

(** [/trans-> idiom] *)
Lemma leq_max m n1 n2 : (m <= maxn n1 n2) = (m <= n1) || (m <= n2).
Proof.
without loss le_n21: n1 n2 / n2 <= n1.
  by case/orP: (leq_total n2 n1) => le_n12; last rewrite maxnC orbC; apply.
by rewrite (maxn_idPl le_n21) orb_idr // => /leq_trans->.
Qed.


(** * Case analisys on type families:
      [case Eq: index / TF]
 *)

(** The difference between
    [alt_spec] and [reflect] *)
Variant alt_spec (P : Prop) (b : bool) : bool -> Type :=
  | AltTrue  of     P : alt_spec P b true
  | AltFalse of  ~~ b : alt_spec P b false.

Lemma altP P b :
  reflect P b -> alt_spec P b b.
Proof.
by move=> Pb; case: b / Pb; constructor.
(** Alternative proof: [by case=> ?; constructor.] *)
Qed.


(** We'll see how to use [altP] later, but let's
    see yet another example of case analysis on
    type families: *)

Lemma sym T (x y : T) :
  x = y -> y = x.
Proof.
(** One could have hoped that pattern-matching on
    a proof of equality would do a rewrite.
    But plain [case] tactic produces a warning:
    "Nothing to inject" warning
    and does nothing.
 *)
case.

(** But if we use a specilized version of [case] tactic for
    type families, we get what is needed:
 *)
move=> eq.
case: y / eq.

Undo 2. Show.

(** Or, equivalently, we can omit the moving step: *)
case: y /.
(** Notice we do case analysis on the proof of [x = y], not on [y]! *)
Show Proof.

done.
Qed.


(** Exercise: transitivity of equality using [case: idx / TF] *)
Lemma trans T (x y z : T) :
  x = y -> y = z -> x = z.
Proof.
    by case: y /.
Qed.


(** [altP] usage *)

(** A spec for boolean equality *)
Variant eq_xor_neq (T : eqType) (x y : T) :
  bool -> bool -> Set :=
  | EqNotNeq of x = y  : eq_xor_neq x y true  true
  | NeqNotEq of x != y : eq_xor_neq x y false false.

Lemma eqVneq (T : eqType) (x y : T) :
  eq_xor_neq x y (y == x) (x == y).
Proof.
rewrite eq_sym.

(* 2nd goal: propositional inequality *)
case: eqP.
Undo.
(* 2nd goal: boolean inequality *)
case: (altP eqP).
- by constructor.
by constructor.
Qed.


(** [apply/view1/view2] idiom:
    Proving equality of booleans by proving
    two implications *)
Lemma ltn_exp2r m n e :
  e > 0 ->
  (m ^ e < n ^ e) = (m < n).
Proof.
move=> e_gt0.
apply/idP/idP.
(* simple proofs by induction for both subgoals *)
Abort.

Goal forall b c,
  ~~ b = b && c.
Proof.
move=> b c.
apply/negP/andP.
Abort.

End BooleanReflection.




(*** Adhoc polymorphism *)

(** * Parametric vs adhoc polymorphism *)

(** Parametric polymorphism is a way to write
    generic functions which work independently
    of the concrete type of the inputs.

    Example: [rev] function on sequences.
 *)

Check @rev : forall (T : Type), seq T -> seq T.

(** Since there is no way for [rev] function to depend
    on concrete values of the elements of the input
    sequence we can conclude that the function' output
    consists of the elements of the input sequence.

    More on this can be found in the paper
    "Theorems for Free" (1989) by P. Wadler
 *)

(** But sometimes we want different behaviours
    for different types.
    The classical example of this is the decidable
    equality operation.
 *)


(* === SLIDES === *)


Module ProductEquality.

Print Canonical Projections.

Fail
  Compute (1, fun (x : nat) => 0) == (2, fun (x : nat) => 0).

Set Printing All.
Check (1, true) == (2, true).
Unset Printing All.

End ProductEquality.


(* === Demo: keying on terms === *)


From mathcomp Require Import bigop.
Import Monoid.

(* keying on terms, as opposed to types *)
Lemma bar m n p q r :
  m + (n + p * (q * r)) = m + n + p * q * r.
Proof.
rewrite !mulmA /=.
done.
Check mulmA.
Print law.
Qed.




(** * Implementation of eqType *)

(**
See "Packaging Mathematical Structures" by
G. Gonthier et al. (2009) for more detail
*)


(** Modules are used mainly as namespaces *)
Module Equality.

(** We connect boolean equality with
    propositional equality *)

(** [reflect] is
    "if and only if" connector on steroids *)
Definition axiom T (e : rel T) :=
  forall x y, reflect (x = y) (e x y).

(** We need mixin-structure to create
    hierarchies of mathematical structures.
    {show telescopes on the whiteboard}
*)

Structure mixin_of T :=
  Mixin {op : rel T; _ : axiom op}.

(** The following means that [eqType] is at
    the top of a hierarchy of structures,
    its heirs would have [class_of] consisting of
    several mixins *)
Notation class_of := mixin_of (only parsing).

Section ClassDef.

(** All the named projections will become keys
    for canonical structures, so we omit the names
    we don't want to become keys.
 *)

Structure type :=
  (** name of the record constructor *)
  Pack
     (** carrier type *)
    {sort;

     (** properties of the structure *)
     _ : class_of sort}.

(** This is to use [type] as [Type] *)
Local Coercion sort : type >-> Sortclass.

Variables (T : Type) (cT : type).

(** Projection out of [type] *)
Definition class :=
  let: Pack _ c := cT return class_of cT in c.

(** We don't define [class] directly in [type]
    because we don't want this projection
    to be added to the canonical structures
    database *)

(** Let's see some coercions at work: *)
Set Printing All.
Print class.
Unset Printing All.

(** cloning constructor of [type] --
    to be discussed later *)
Definition clone :=
  fun c & cT -> T & phant_id (@Pack T c) cT => Pack c.

End ClassDef.

Module Exports.

(** We have to repeat coercion declarations here
    because those do not survive sections *)
Coercion sort : type >-> Sortclass.
(** Some shorthands *)
Notation eqType := type.
(** e.g. we can now say [eqType]
    instead of [Equality.type] *)
Notation EqMixin := Mixin.
Notation EqType T m := (@Pack T m).

Notation "[ 'eqMixin' 'of' T ]" :=
  (class _ : mixin_of T)
    (at level 0, format "[ 'eqMixin'  'of'  T ]")
    : form_scope.
Set Printing Coercions.
About class.
Unset Printing Coercions.

(** When we say, for instance, [eqMixin of nat]
    actually means [(class _ : mixin_of nat)],
    and Coq is facing the following
    unification problem:

class ?e : mixin_of (sort ?e)
vs
class ?e : mixin_of nat

which is equivalent to

(sort ?e) ≡ nat

so the canonical structures mechanism
is able to resolve that.
*)

Notation "[ 'eqType' 'of' T 'for' C ]" :=
  (@clone T C _ idfun id)
  (at level 0, format "[ 'eqType'  'of'  T  'for'  C ]") : form_scope.
Notation "[ 'eqType' 'of' T ]" :=
  (@clone T _ _ id id)
    (at level 0, format "[ 'eqType'  'of'  T ]") :
    form_scope.

End Exports.

End Equality.
Export Equality.Exports.



(** Here is the projection we actually need *)
Definition eq_op T :=
  Equality.op (Equality.class T).

Lemma eqP T : Equality.axiom (@eq_op T).
Proof. by case: T => ? []. Qed.
Arguments eqP {T x y}.

Delimit Scope eq_scope with EQ.
Open Scope eq_scope.

Notation "x == y" := (eq_op x y)
  (at level 70, no associativity) : bool_scope.

Notation "x == y :> T" := ((x : T) == (y : T))
  (at level 70, y at next level) : bool_scope.

Notation "x != y" := (~~ (x == y))
  (at level 70, no associativity) : bool_scope.

Notation "x != y :> T" := (~~ (x == y :> T))
  (at level 70, y at next level) : bool_scope.

Notation "x =P y" :=
  (eqP : reflect (x = y) (x == y))
  (at level 70, no associativity) : eq_scope.

Notation "x =P y :> T" :=
  (eqP : reflect (x = y :> T) (x == y :> T))
  (at level 70, y at next level, no associativity) : eq_scope.

Prenex Implicits eq_op eqP.


Section BasicLemmas.
Lemma eq_refl (T : eqType) (x : T) : x == x.
Proof. by apply/eqP. Qed.
End BasicLemmas.

Hint Resolve eq_refl.



(** Exercise:
  Implement an instance of equality type for the [seq] datatype
  and test it
 *)




(*** Overview *)
(**

Tactics:
- [case: idx / TF] -- case analisys for type families (indexed types)
- [apply/view1/view2] for boolean equalities

Idioms:
- [move/leq_trans->]

Canonical structures and mathematical structures:
- eqType for ground types and parameterized types

Coercions:
- [sort]

*)




