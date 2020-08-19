From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** Draw on the whiteboard a picture of a dependent function space, as an infinite cartesian product *)


(** Eliminating existential quantifier *)

Definition elim_example T (A : T -> Prop) (C : Prop) :
  (forall x : T, A x -> C) -> ((exists x : T, A x) -> C)
:=
  fun (xac : forall x : T, A x -> C) =>
    fun (x_ax : exists x : T, A x) =>
      match x_ax in (ex _)   (* [in] and [return] annotations may be skipped here *)
            return C
      with
      | ex_intro x ax => xac x ax
      end.

(** Exercise *)
Definition elim_exercise T (A : T -> Prop) (C : Prop) :
  ((exists x : T, A x) -> C) -> (forall x : T, A x -> C)
:=
  fun ec x ax =>
    ec (ex_intro A x ax).


(** One distinct feature of Coq is that it has a number of dependent pair types
    looking a lot like the [ex] type.
    Namely, [sig] and [sigT] types. Let's look at them more closely and compare with [ex]. *)

Module MyNamespace.

(** You should pay attention to the type annotations of
    [A] and [P] parameters for each of the definitions below. *)

Inductive ex (A : Prop) (P : A -> Prop) : Prop :=
| ex_intro : forall x : A, P x -> ex P.
(** [ex] models the contructivistic existential quantifier,
    because every [ex]'s parameter lives in [Prop], the universe of
    purely logical entities, and [ex P] also belongs to [Prop] universe
 *)

Inductive sig (A : Type) (P : A -> Prop) : Type :=
| exist : forall x : A, P x -> sig P.
(** [sig] models the so-called subset type, which is a piece of data (of type [A])
    and a proof that that piece of data satisfies a property [P].
    Here, [A] is a [Type] and not a proposition, meaning it is computationally relevant.
    [sig P] belongs to [Type], i.e. as a whole it's a piece of data.
    On the other hand, the proof of [P x] is computationally irrelevant.
 *)

Inductive sigT (A : Type) (P : A -> Type) : Type :=
| existT : forall x : A, P x -> sigT P.
(** [sigT] is a so-called sigma type.
    It's a dependent pair of two computationally relevant entities (data),
    for which the type of the second component depends on the value of the first one.
    The whole thing ([sigT P]) is also computationally relevant.
 *)

End MyNamespace.


(** We will talk about [ex], [sig] and [sigT] in a greater detail later on in this course.
    For now let's just show one simple example for [sig] type.
    Below, the notation {x : T | P x} stands for [sig P].
    Let's write yet another implementation of our beloved predecessor function on [nat].
 *)

Definition pred (n : {x : nat | x != 0}) : nat :=
  match n with
  | exist x proof_x_neq_0 => predn x
  end.
(** Exercise: figure out what [x != 0] means here *)


(** To use [pred] function we must provide a number and a proof that it's not a zero *)
Compute pred (exist (fun x => x != 0) 42 erefl).
Check erefl : pred (exist _ 42 erefl) = 41.
(** Notice that we provide the predicate expressing that the input number is non-zero explicitly.
    Actually, Coq can infer this predicate if we ask to do it for us using an underscore: *)
Compute pred (exist _ 42 erefl).


(** Let's try and see what happens if we use [ex] instead of [sig] type *)
Fail Definition pred_fail (n : exists x, x != 0) : nat :=
  match n with
  | ex_intro x proof_x_neq_0 => predn x
  end.
(**
We get an error message:

Incorrect elimination of "n" in the inductive type "ex":
the return type has sort "Set" while it should be "SProp" or "Prop".
Elimination of an inductive object of sort Prop is not allowed on a predicate in sort Set
because proofs can be eliminated only to build proofs.

It says that we cannot use proofs to build data. And the reason behind this
restriction we will learn later in the course.
*)



(** Exercise: show that [ex] is a more general case of [and].
    This is because terms of type [ex] are dependent pairs, while terms of type [and]
    are non-dependent pairs, i.e. the type of the second component in independent of the
    value of the first one. *)

Definition and_via_ex (A B : Prop) :
  (exists (_ : A), B) <-> A /\ B
:=
  conj (fun '(ex_intro a b) => conj a b)
       (fun '(conj a b) => ex_intro (fun _ => B) a b).



(** * Proofs by induction *)

Module MyNamespace2.
Definition addn0 :
  forall n : nat, n + 0 = n
:=
  fix rec (n : nat) : n + 0 = n :=
    match n return (n + 0 = n) with
    | O => erefl 0
    | S n' => congr1 S (rec n')
    end.

(** Notice that the symmetric lemma does not require recursion: *)
Definition add0n :
  forall n : nat, 0 + n = n
:=
  fun n : nat => erefl n.
(** Exercise: why don't we need recursion here but not for [addn0]? *)


(** Exercise: *)

Definition addnS :
  forall m n, m + n.+1 = (m + n).+1
:=
  fix rec m :=
    fun n => match m with
             | O => erefl
             | S m' => congr1 S (rec m' n)
             end.


(** Optional exercise (for the bored student): *)
(* Definition addnCA : left_commutative addn := *)

(** Optional exercise (for the bored student): *)
(* Definition addnC : commutative addn *)



(** Usually, a lemma like [addn0] would be proven using
    the principle of mathematical induction:  *)

(** Principle of Mathematical Induction *)

Definition nat_ind :
  forall (P : nat -> Prop),
    P 0 ->
    (forall n : nat, P n -> P n.+1) ->
    forall n : nat, P n
:=
  fun P =>
    fun (p0 : P 0) =>
    fun (step : (forall n : nat, P n -> P n.+1)) =>
    fix rec (n : nat) :=
      match n return (P n) with
      | O => p0
      | S n' => step n' (rec n')
      end.

(** In type theory induction is just recursion! *)


(** Here is yet another way of proving [addn0] where we
    factor out recursion and re-use [nat_ind]: *)
Definition addn0' :
  forall n : nat, n + 0 = n
:=
  @nat_ind
    (fun n => n + 0 = n)
    (erefl 0)
    (fun _ pn => congr1 S pn).

(** In general a principle like [nat_ind] is called an eliminator (or recursor, or recursion scheme)
    and it can have a more general type like the following one: *)
Definition nat_rect :
  forall (P : nat -> Type),
    P 0 ->
    (forall n : nat, P n -> P n.+1) ->
    forall n : nat, P n
:=
  fun P =>
    fun (p0 : P 0) =>
    fun (step : (forall n : nat, P n -> P n.+1)) =>
    fix rec (n : nat) :=
      match n return (P n) with
      | O => p0
      | S n' => step n' (rec n')
      end.

(** [nat_rect] can be used to implement e.g. the addition function *)
Definition addn' : nat -> nat -> nat
:=
  @nat_rect
    (fun _ => nat -> nat)
    id
    (fun _ pn => succn \o pn).

Compute addn' 21 21.
Compute addn' 2 9.
Compute addn' 9 2.
Compute addn' 0 0.
Compute addn' 9 0.

(** It can be proved that [addn] and [addn'] are equivalent,
    i.e. [addn =2 addn'], which means [forall x y, addn x y = addn' x y] *)


End MyNamespace2.


(** * The SSReflect proof language *)

Lemma A_implies_A :
  forall (A : Prop), A -> A.
Proof. (* <-- optional *)
move=> A.     (* => tactical *)
Show Proof.
move=> prfA.
Show Proof.
(* move: a. exact. *)
exact: prfA.
Show Proof.
Qed.

(**
[=>] is a tactical, it takes a tactic and a list of "actions",
[tac=> act1 act2 ... actn].
First, Coq applies the tactic [tac] to the "top" of the "goal stack",
i.e. to the first antecendent if the goal is an implication.
And then it executes actions from left to right.
If an action is an identifier then it gets introduced to
the context.

[move] is like a no-operation tactic needed mostly because
[=>] needs a tactic to the left of itself.

(Note: actually [move] converts the goal to the head normal form,
       but let us ignore this for now.)

[exact] tactic tells Coq the exact solution of the current subgoal.
 *)

Lemma or_and_distr A B C :
  (A \/ B) /\ C -> A /\ C \/ B /\ C.
Proof.
case.
case.
- move=> a. move=> c. left. split.
  - exact: a.
  by apply: c.
move=> b c. right. by split.
Qed.

(**
[case] tactic, as most SSReflect tactics applies to the top of
the goal stack, and translates into pattern-matching at the term level.
E.g. if the top of the goal stack is a conjunction then
the top gets removed and two new conjuncts get pushed on
the goal stack.
If the top of the goal stack is a disjunction then
the top of the stack gets consumed and Coq generates two
subgoals corresponding to the left and right disjuncts.

[left] tactic tells Coq that we are going to prove the disjunctive goal at hand by proving the left disjunct.
[right] does the same but for the right disjunct.

[split] tactic applies to a conjunctive goal and splits it
into two new subgoals corresponding to the left and right
conjuncts.

[move=> a. move=> b.] us usually replaced by a more concise
[move=> a b.] tactic expression.

[apply] tactic applies the top of the goal stack to the rest of the
goal stack (it's better to see how it work by example), it
involves the so-called "backward" reasoning. It's when
we start with the goals conclusion and work our way up by
proving assumtions needed to finish the proof.

The [:] colon tactical moves a hypothesis from the context into
the goal (it becomes the top of the goal stack).
So [apply: foo] actually moves hypothesis [foo] from the context
to the goal and applies the current top of the goal stack
to the rest of it.
If you need to apply a hypothesis to the goal and still
keep it in the context, use parentheses around the hypothesis name:
[apply: (foo)].
Also, [move: foo] just moves a hypothesis [foo] back onto the
goal stack. In a sense it's a reversal of [move=> foo].

[by] tactical takes a list of tactics (or a single tactic),
applies it to the goal and then tries to finish the proof
using some simple proof automation.
E.g. [by []] means "the proof of the goal is trivial", because
Coq does not need any hints from the user.
This is equivalent to using the [done] tactic.

[by], [exact] and [done] are called "terminators" because
if these do not solve the goal completely, the user gets
an error message.
It is advised to put the terminators to mark where the current
subgoal is proven completely. This helps fixing proofs when they breakdue to e.g. changes in the definitions of the project.
 *)

About or_and_distr.


(* a terser version *)
Lemma or_and_distr' A B C :
  (A \/ B) /\ C -> A /\ C \/ B /\ C.
Proof.
by move=> [ [a | b] c ]; [left | right].
Qed.

(**
One of the actions supported by the [=>] tactical is [[]] (square brackets). It roughly corresponds to [case] tactic.

The [;] tactical (semicolon) is used to compose several tactics
into a pipeline. To execute [tac0; [tac1 | tac2 | ... | tacn]]
Coq first executes [tac0] tactic generating [n] subgoals
and then applies [tac1] to the first subgoal, [tac2] to the
second one and so on. If there is a mismatch between the number of
subgoals and the number of supplied tactics you'll see an error message. The user is allowed to skip some tactics (or all of them),
but the corresponding [|] (pipe) symbols must be provided,
i.e. [tac0; [| tac2 |]] executes like so: first [tac0] gets applied and
generate 3 subgoals, then [tac2] gets applied to the second subgoal.
*)

(* An example taken from
"An Ssreflect Tutorial" by G.Gonthier, R.S. Le(2009) *)
Section HilbertSaxiom.

Variables A B C : Prop.

Lemma HilbertS :
  (A -> B -> C) -> (A -> B) -> A -> C.
Proof.
move=> hAiBiC hAiB hA.
move: hAiBiC.
apply.
- by [].
by apply: hAiB.
Qed.

End HilbertSaxiom.

Section Rewrite.

Variable A : Type.
Implicit Types x y z : A.

Lemma eq_reflexive x :
  x = x.
Proof. by []. Qed.


Lemma eq_sym x y :
  x = y -> y = x.
Proof.
move=> x_eq_y. rewrite -x_eq_y. by [].
Qed.

(** [rewrite] tactic lets us use equations.
    If [eq : x = y] then [rewrite eq] changes [x]'s in the goal
    to [y]. [rewrite -eq] does the rewriting in the opposite direction.
 *)

Lemma eq_sym_shorter x y :
  x = y -> y = x.
Proof.
by move=> ->.
Qed.

(**
The [=>] tactical supports [->] action. This action uses the top
of the goal stack (which must be an equation) and does rewriting.
There is also the symmetrical [<-] action.

[move=>->] corresponds to something like this
[move=> fresh_name; rewrite {}fresh_name],
where [rewrite {}eq] means rewrite with [eq] equation and clear
it off the context.
*)

Lemma eq_trans x y z :
  x = y -> y = z -> x = z.
Proof.
by move=> ->.
Qed.

