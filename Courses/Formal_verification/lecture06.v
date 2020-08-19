From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(*** Induction *)


(** * Simple induction *)

Lemma addnA :
  associative addn.
Proof.
Print associative.
(** To unfold a definition use [rewrite /definition] *)
rewrite /associative.
move=> x y z.
(** but the above solution if not idiomatic, the experienced user
    knows what [associative] looks like, and [=>] tactical can look inside
    of definitions *)
Restart. Show.
move=> x y z.
(** Proving this lemma needs induction which we can ask Coq to use with [elim] tactic.
    We'd like to do induction on the variable [x].
    But, as usual, [elim] operates on the top of the goal stack, so
    we need to put back [x] into the goal: *)
move: x.
elim.   (** induction over [x] in this case *)
Show Proof.
(** Notice that [elim] uses [nat_ind] induction principle under the hood. *)
- (** the base case *)
  (** actually, the goal looks like this [0 + (y + z) = (0 + y) + z] now,
      because the notation for addition is a left associative,
      but Coq won't show those extra parentheses *)
  (** [0 + (y + z)] reduces into [y + z] and
      [0 + y] reduces to [y], hence
      the goal is equivalent to [y + z = y + z],
      i.e. it can be solved trivially. *)
  by [].
(** the inductive step *)
move=> x IHx.  (** [IH] stands for "induction hypothesis" *)
Fail rewrite IHx.
(** To use [IHn] we need to change the goal to contain e.g.
    [n + (y + z)].
    To achieve this we need to use a lemma which lets us simplify
    [x.+1 + y] into [(x + y).+1]. Let's use the [Search] mechanism
    to find such a lemma: *)
Search _ (?x.+1 + ?y).      (** You almost always want to use the underscore symbol [_] after [Search] *)
(** This query returns a list of lemmas and a brief examination shows
    [addSn] is the lemma we are looking for *)
(** See https://github.com/math-comp/math-comp/wiki/Search to find out
    more about how to use the [Search] command. *)
rewrite addSn.
(** Now we can use the induction hypothesis *)
rewrite IHx.
(** We could use [addSn] to change the right-hand side (RHS) of the goal to be
    identical to the left-hand side (LHS), but it is not necessary because
    the RHS is convertible to the LHS (i.e. the RHS reduces to the LHS) *)
done.

(** Let's simplify the proof now: *)

(** 1. [move: x. elim.] can be refactored into [elim: x.]. *)

(** 2. We saw that the first subgoal was trivially provable.
       This is a very frequent case, so SSReflect provides a special
       "switch" [//] (double slash) to handle such cases "on the fly".
       We change
          elim: x.
          - by [].
       into
          elim: x=> //.
       This means "do induction on [x] and try to solve the generated subgoals automatically"
 *)
Restart. Show.
move=> x y z.
elim: x=> //.
move=> x IHx.

(** 3. Again, [elim: x=> //. move=> x IHx.] can be fused into
       [elim: x=> // x IHx.] *)

(** 4. [rewrite addSn. rewrite IHx.] can be simplified into [rewrite addSn IHx.] *)

Restart. Show.

(** 5. Combining all the above together, we get finally: *)

by move=> x y z; elim: x=> // x IHx; rewrite addSn IHx.
Qed.


(** Exercise *)
Lemma addn0 :
  right_id 0 addn.
Proof.
Admitted.  (** <- We can ask Coq to believe us that we can prove this lemma later *)

(** If admitted, [addn0] can be used in later proofs.
    Beware of this feature -- you might admit an unprovable (or worse,
    contradictory) statement and rely on it throughout your project. *)

(** Often times, we introduce variables into context right away
    by stating lemmas in this manner:
    [addSnnS m n : m.+1 + n = m + n.+1]
    as opposed to
    [addSnnS : forall m n, m.+1 + n = m + n.+1] *)
(** Exercise *)
Lemma addSnnS m n :
  m.+1 + n = m + n.+1.
Proof.
Admitted.

Lemma addnC :
  commutative addn.
Proof.
move=> x y.
elim: x.
  - rewrite addn0. rewrite add0n. done.
  - move=> x IHx.
    rewrite addSn.
    rewrite IHx.
    rewrite -addSnnS.
    rewrite addSn.
    done.
Qed.


(** * Generalizing Induction Hypothesis *)

(** The standard (non-tail-recursive) factorial function *)
Locate "`!".
Print factorial.
Print fact_rec.  (* non-tail-recursive implementation *)

(** A tail-recursive implementation *)
(** [k] is usually called "accumulator" *)
Fixpoint factorial_mul (n : nat) (k : nat) : nat :=
  if n is n'.+1 then
    factorial_mul n' (n * k)
  else
    k.

(** The iterative implementation of the factorial function *)
Definition factorial_iter (n : nat) : nat :=
  factorial_mul n 1.

(** Let's prove our optimized implementation of factorial is correct *)
Lemma factorial_mul_correct n k :
  factorial_mul n k = n`! * k.
Proof.
elim: n.
- (** Let us simplify the goal by telling Coq to perform some reduction steps for us
    using the [/=] switch.
    If you are familiar with standard Coq, [/=] switch is equivlent to the [simpl] tactic.
   *)
  unfold factorial_mul.  
  move=> /=.
  (** Notice that simplification didn't work for the RHS.
      This is because the implementations of the common arithmetic
      functions block reduction using the [nosimpl] SSReflect idiom.
      This is done to better control the shape of expressions and
      not let reduction (which is hard to control in a fine-grained manner)
      mangle our expressions so that [rewrite] tactic would not work on them. *)
  (** Now, let's find a lemma which would simplify the RHS for us: *)
  Search _ (0`!).
  rewrite fact0.
  Fail done.
  (** This fails because [1 * k] reduces to [k + 0] which
      is _not_ equal to [k] definitionally. Hence, we need a lemma to
      simplify [1 * k] into [k]. Let's use [Search] to find it. *)
  Search _ (1 * _).
  (** This finds nothing, because this sort of lemma is formulated using
      [left_id] defintion. Since [left_id] would return a bit too many
      lemmas, let's narrow the search space down by telling the [Search]
      command to restrict the search result to containing _both_
      [left_id] and [muln] definitions. *)
  Search _ left_id muln.
  (** Checkout the linked wiki page, https://github.com/math-comp/math-comp/wiki/Search,
      for more gotchas like the one above *)
  by rewrite mul1n.
move=> n IHn /=.
(** And now we are kind of stuck. Here is a number of steps
    we could do, but those would still lead nowhere *)
Search _ (_.+1`!).
rewrite factS.
rewrite -mulnA.
rewrite -IHn.

(** This is happening because the induction hypothesis
    is not general enough -- it fixes the value of
    the accumulator to be [k], whereas we would want it
    to work for any accumulator. *)
Restart. Show.

(** First, let us generalize our goal w.r.t. to [k] *)
move: k.
elim: n; first by move=> k; rewrite fact0 mul1n.
move=> n IHn.
(** Now we can see the induction hypothesis is generalized and works for any [k] *)
move=> k /=.
rewrite IHn.
rewrite factS.
(** Here you could use the fact that multiplication is left commutative and associative: *)
About mulnCA.
Print left_commutative.
rewrite mulnCA.
rewrite mulnA.
done.

Restart. Show.

(** Refactoring all the steps above results in a proof script like the following one: *)

elim: n k=> [|n IHn] k; first by rewrite fact0 mul1n.
by rewrite factS /= IHn mulnCA mulnA.
(** Notice we can use [/=] switch with [rewrite] tactic.
    And, in fact, [//] switch too. *)
Qed.

Lemma factorial_iter_correct n :
  factorial_iter n = n`!.
Proof.
by rewrite /factorial_iter factorial_mul_correct muln1.
Qed.


(** * Custom Induction Principles *)

(** Let's define a recursive Fibonacci function for the illustration purposes *)

(** Coq cannot figure out that we are using
    structural recursion here, because it does not see
    [n''.+1] is a subterm of [n]. It needs a hint. *)
Fail Fixpoint fib (n : nat) : nat :=
  if n is n''.+2 then fib n'' + fib n''.+1
  else n.

(** Here is the hint: name a structural subterm explicitly
    using [as]-annotation *)
Fixpoint fib (n : nat) : nat :=
  if n is (n''.+1 as n').+1 then fib n'' + fib n'
  else n.

(** Illustrate how [simpl nomatch] works *)

Section Illustrate_simpl_nomatch.
Variable n : nat.

Lemma default_behavior :
  fib n.+1 = 0.
Proof.
move=> /=.  (* fib n.+1 should not get simplified *)
Abort.

(** Let's forbid generating  *)
Arguments fib n : simpl nomatch.

Lemma after_simpl_nomatch :
  fib n.+2 = 0.
Proof.
move=> /=.  (* this is what we want *)
Abort.

End Illustrate_simpl_nomatch.


(** The results of the [Arguments] command does not survive
    sections so we have to repeat it here *)
Arguments fib n : simpl nomatch.


(** And here is a more efficient iterative version *)
Fixpoint fib_iter (n : nat) (f0 f1 : nat) : nat :=
  if n is n'.+1 then fib_iter n' f1 (f0 + f1)
  else f0.

Arguments fib_iter : simpl nomatch.

(** One-step simplification lemma *)
Lemma fib_iterS n f0 f1 :
  fib_iter n.+1 f0 f1 = fib_iter n f1 (f0 + f1).
Proof. by []. Qed.

Lemma fib_iter_sum n f0 f1 :
  fib_iter n.+2 f0 f1 =
  fib_iter n f0 f1 + fib_iter n.+1 f0 f1.
Proof.
(** Notice we generalize IH here *)
elim: n f0 f1 => [//|n IHn] f0 f1.
by rewrite fib_iterS IHn.
Qed.


Lemma fib_iter_correct n :
  fib_iter n 0 1 = fib n.
Proof.
elim: n=> // n IHn.

(** We have used [//=] switch here -- it combines *)
(*     [//] and [/=] into one. *)
(** And we are stuck again. The induction hypothesis is not general enough. *)
(** To understand better what is going we can case-split on [n] one more time: *)
case: n IHn => // n IHn.
rewrite fib_iter_sum.
rewrite IHn.
(** Now we see that we lack an induction hypothesis for [fib_iter n 0 1].
    Informally, ordinary induction works using the induction step from the
    previous value of [n], but [fib] uses two previous values to compute
    the next Fibonacci number. *)
Abort.

(** We can design a custom induction principle to resolve the issue:

    Lemma nat_ind2 (P : nat -> Prop) :
      P 0 ->
      P 1 ->
      (forall n, P n -> P n.+1 -> P n.+2) ->
      forall n, P n.

    Compare this to the ordinary induction principle:

    Lemma nat_ind (P : nat -> Prop) :
      P 0 ->
      (forall n, P n -> P n.+1) ->
      forall n, P n.
*)


(** First, a helper lemma. It let's us duplicate an assumption in
    the goal stack. *)
Lemma dup {A} : A -> A * A. Proof. by []. Qed.
(* Notation apply := (ltac:(let f := fresh "_top_" in move=> f {}/f)). *)

(** This induction principle repeats, in a sense,
    the structure of the (recursive) Fibonacci function *)
Lemma nat_ind2 (P : nat -> Prop) :
  P 0 ->
  P 1 ->
  (forall n, P n -> P n.+1 -> P n.+2) ->
  forall n, P n.
Proof.
move=> p0 p1 Istep n.
(** If we did ordinary induction we would get ourselves into
    the same trap as with [fib_iter_correct] lemma.
    So let's prove a _stronger_ goal instead.
    Why stronger goal? Because a stronger goal results in a stronger
    induction hypothesis! *)
suffices: P n /\ P n.+1.       (** <- [suffices] tactic *)
(** This generates two subgoals:
    1. It makes us show that the new goal suffices to prove the old one.
    2. It makes us prove the new goal. *)
- by case.
elim: n.
- by split.
move=> n.
case.
(** Here we use the view mechanism of SSReflect: [move /Hyp] behaves
    somewhat like [move=> fresh; move: (Hyp fresh)], modulo
    some argument inference. So it's like applying a hypothesis
    to the top of the goal stack. *)
move=> fresh.
(** If we do the second step literally as above, it will fail. *)
Fail move: (Istep fresh).
(** Coq can figure out the first argument of [Istep]: *)
move: (Istep _ fresh).
(** This is what is going on here: *)
Undo 3. Show.
move/Istep.
move=> pn12.
move/dup.
move=> [].
move/pn12.
done.

(** Combining the above into a more or less idiomatic solution: *)
Restart. Show.

move=> p0 p1 Istep n; suffices: P n /\ P n.+1 by case.
by elim: n=> // n [/Istep pn12] /dup[/pn12].
Qed.



(** Now we can apply the custom induction principle we just proved
    using [elim/ind_principle] version of the [elim] tactic.
    Notice that the slash symbol here does _not_ mean "view" as in [move /View].
 *)
Lemma fib_iter_correct n :
  fib_iter n 0 1 = fib n.
Proof.
elim/nat_ind2: n=> // n IHn1 IHn2.
by rewrite fib_iter_sum IHn1 IHn2.
Qed.
(** Note: fib_iter_correct can be proven using [suffices] tactic:
     (fib_iter n 0 1 = fib n /\ fib_iter n.+1 0 1 = fib n.+1).
 *)


(** * Another way is to provide a spec for fib_iter *)


From Coq Require Import Psatz.  (* to use [lia] tactic *)

(**
- [lia] is a solver for Linear Integer Arithmetic
*)

(** Sometimes instead of a custom induction principle we can
    come up with a different formulation of the specification.*)

Lemma fib_iter_spec n f0 f1 :
  fib_iter n.+1 f0 f1 = f0 * fib n + f1 * fib n.+1.
Proof.
elim: n f0 f1=> [|n IHn] f0 f1; first by rewrite muln0 muln1.
rewrite fib_iterS IHn /=.
(** We can use a bit of automation to finish off the proof.
    Note that [lia] cannot handle SSReflect's arithmetic operations,
    so we need to massage the goal and switch to the standard
    implementations of the arithmetic functions.
 *)
by rewrite -!plusE -!multE; lia.

Restart. Show.

(** Manual solution *)
elim: n f0 f1=> [|n IHn] f0 f1; first by rewrite muln0 muln1.
by rewrite fib_iterS IHn /= mulnDr mulnDl addnCA.
Qed.

Lemma fib_iter_correct' n :
  fib_iter n 0 1 = fib n.
Proof.
by case: n=> // n; rewrite fib_iter_spec mul1n.
Qed.



(** * Yet another solutiton *)

(* due to D.A. Turner, see his "Total Functional Programming" (2004) paper *)
(** Exercise *)
Lemma fib_iter_spec' n p :
  fib_iter n (fib p) (fib p.+1) = fib (p + n).
Proof.
Admitted.

(** Exercise *)
Lemma fib_iter_correct'' n :
  fib_iter n 0 1 = fib n.
Proof.
Admitted.




(** * Complete induction *)

(** It's also called:
    - strong induction;
    - well-founded induction;
    - course-of-values induction
 *)

Fixpoint div2_helper (res n : nat) : nat :=
 match n with
   | O       => res
   | S O     => res
   | S (S k) => div2_helper (S res) k
 end.

Definition div2 (n : nat) : nat := div2_helper O n.

(** Exercise *)
Lemma lt_wf_ind (P : nat -> Prop) :
  (forall m, (forall k : nat, (k < m) -> P k) -> P m) ->
  forall n, P n.
Proof.
  move=> Pm.
  
Admitted.


(** Exercise *)
Lemma fib_iter_correct''' n :
  fib_iter n 0 1 = fib n.
Proof.
elim/ltn_ind: n.
Admitted.




(** Overview.
Switches:
- Simplification switch [/=]
- Switch to resolve trivial goals [//]
- Sombining the previous ones into one switch [//=]

Tactics:
- [elim] -- uses the default induction principle ([nat_ind] for the natural numbers)
- [elim/custom_induction_principle] -- we specify the induction principle by hand
- View mechanism: [move/view_lemma]
- [suffices]
*)
