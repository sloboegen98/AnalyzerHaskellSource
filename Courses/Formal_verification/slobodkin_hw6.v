From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** Use SSReflect tactics.
    DO NOT use automation like [tauto], [intuition], [firstorder], etc.,
    except for [by], [done], [exact] tactic(al)s. *)




Section BooleanLogic.

(** Prove boolean implication is transitive.
    Your final proof version must be a one-liner using
    just one tactic and a number of switches. *)
Lemma implb_trans : transitive implb.
Proof.
(* by <tactic>=> <switches>. *)
  by move=> x y z; case: x; case: y.
Qed.


(** [==] is the decidable equality operation for types with decidable equality.
    In case of booleans it means [if and only if]. *)
Fixpoint mostowski_equiv (a : bool) (n : nat) :=
  if n is n'.+1 then mostowski_equiv a n' == a
  else a.

(** The recursive function above encodes the following classical
    propositional formula:
    [((A <-> A ...) <-> A) <-> A]
    For instance, if n equals 3 then the formula look like this
    [((A <-> A) <-> A) <-> A]
    Since we work in the classical propositional fragment
    we can encode the [<->] equivalence with boolean equality [==].
 *)

(** Try to come up with a one-line proof *)
Lemma mostowski_equiv_even_odd a n :
  mostowski_equiv a n = a || odd n.
Proof.
  elim: n => //=.
  - by case: a.
  - move=> n.
    by case: (mostowski_equiv a n);
     case: a=> //=; 
     move=> H //=; elim: H.
Qed.

End BooleanLogic.


(* Search subn0. *)

Section Arithmetics.


Lemma subn0 : right_id 0 subn.
Proof.
  move=> x.
  by case: x.
Qed.


Fixpoint triple (n : nat) : nat :=
  if n is n'.+1 then (triple n').+3
  else n.

Lemma triple_mul3 n :
  triple n = 3 * n.
Proof.
  elim: n => //=.
  move=> n H.
  rewrite mulnS H=> //.
Qed.
(** Hint: use [Search _ (<pattern>).] to find a useful lemma about multiplication *)

Lemma double_inj m n :
  m + m = n + n -> m = n.
Proof.
  rewrite addnn addnn.
  apply: double_inj.
Qed.


(** Write a tail-recursive variation of the [addn] function
    (let's call it [addn_iter]).
    See https://en.wikipedia.org/wiki/Tail_call
 *)

Fixpoint add_iter (n m : nat) {struct n}: nat :=
  if n is n'.+1 then (add_iter n' m.+1)
  else m.

Lemma add_iter_correct n m :
  add_iter n m = n + m.
Proof.
  move: m.
  elim: n=> //=.
  move=> n.
  - move=> H m. 
    rewrite addSnnS.
    apply: H.
Qed.

Lemma dup {A} : A -> A * A. Proof. by []. Qed.

Lemma nat_ind2 (P : nat -> Prop) :
  P 0 ->
  P 1 ->
  (forall n, P n -> P n.+1 -> P n.+2) ->
  forall n, P n.
Proof.
  move=> p0 p1 Istep n; suffices: P n /\ P n.+1 by case.
  by elim: n=> // n [/Istep pn12] /dup[/pn12].
Qed.

Fixpoint fib (n : nat) : nat :=
  if n is (n''.+1 as n').+1 then fib n'' + fib n'
  else n.
Arguments fib n : simpl nomatch.

Lemma addn2eq m n r s 
  (EQmn: m = n)
  (EQrs: r = s) :
  m + r = n + s.
Proof.
  by rewrite EQmn EQrs.
Qed.


Lemma fib_add_succ m n :
  fib (m + n).+1 = fib m.+1 * fib n.+1 + fib m * fib n.
Proof.
  elim: m n => [| m IHm] n.
  - by rewrite addn0 mul1n add0n.
  rewrite addSnnS.
  (* Search _ (?m +?n.+1). *)
  rewrite addnS.
  move=> //=.
  rewrite mulnDl.
  rewrite IHm.
  rewrite addnC.

  rewrite -IHm.

Qed.

  (** Optional exercise *)
(** Hint: this lemmas does not require induction,
          just look for a couple lemmas *)
Lemma leq_add1l p m n :
  m <= n -> m <= p + n.
Proof.
  by move/leq_trans=> -> //; apply: leq_addl.
Qed.


(** Optional exercise *)
(** Hint: you might want to reuse [leq_add1l] lemma *)
(* Lemma fib_monotone m n :
  m <= n -> fib m <= fib n.
Proof.
Qed. *)


(** Optional exercise: Strong induction principle *)
(* Lemma lt_wf_ind (P : nat -> Prop) :
  (forall m, (forall k : nat, (k < m) -> P k) -> P m) ->
  forall n, P n.
Proof.
Qed. *)

End Arithmetics.




Section RewriteExercises.

(** Find a sequence of rewrites to prove the lemmas inside this section.
    Use [Search] command to look for suitable lemmas. *)
    
Lemma addnCB m n : m + (n - m) = m - n + n.
Proof.
  rewrite (addnC (m - n)) -!maxnE.
  apply: maxnC.
Qed.

Lemma subn_sqr m n : m ^ 2 - n ^ 2 = (m - n) * (m + n).
Proof.
  (* rewrite -!mulnn. *)
  (* rewrite mulnBl. *)
  (* rewrite !mulnDr. *)
  (* rewrite addnC. *)
  (* rewrite mulnC. *)
  (* rewrite subnDl. *)
  (* done. *)
  by rewrite -!mulnn mulnBl !mulnDr addnC mulnC subnDl.
Qed.


(** Optional exercise.
    [negb \o odd] means "even".
    The expression here says, informally,
    the sum of two numbers is even if the summands have the same "evenness",
    or, equivalently, "even" is a morphism from [nat] to [bool] with respect
    to addition and equivalence correspondingly.
    Hint: [Unset Printing Notations.] and [rewrite /definition] are your friends :)
 *)
Lemma even_add :
  {morph (negb \o odd) : x y / x + y >-> x == y}.
Proof.
Qed.


End RewriteExercises.
