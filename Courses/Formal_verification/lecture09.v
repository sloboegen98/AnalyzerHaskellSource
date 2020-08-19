From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(*** Validation
     vs
     Verification
 *)

(**
_Validation_ is the process of checking whether the specification
describes the so-called real world (or corresponds to the needs
of the user).

_Verification_ is the process of checking that the software
meets the specification.

In this course we mostly focus on verification, but also touch
upon validation using simple classical examples.
 *)


(*** Sorting algorithms *)

(** * Insertion sort *)

Module Insertion.
Section InsertionSort.

Variable T : eqType.
Variable leT : rel T.
Implicit Types x y z : T.
Implicit Types s t u : seq T.

(** Insert an element [e] into a sorted list [s] *)
Fixpoint insert e s : seq T :=
  if s is x :: s' then
    if leT e x then
      e :: s
    else
      x :: (insert e s')
  else [:: e].

(** Sort input list [s] *)
Fixpoint sort s : seq T :=
  if s is x :: s' then
    insert x (sort s')
  else
    [::].


(**
Now we'd like to prove [sort] functionally correct.
"Functionally" means here "as a relation between the input
and output". Notice that we don't treat the question of
time/space complexity. I'll use "correct" as a synonym for
"functionally" correct in the following discussion.

If you'd like to see how specify complexity, you
might want to check "A Machine-checked Proof of
the Average-case Complexity of Quicksort in Coq"
by van der Weegen and McKinna (2008)


What does mean for a sorting algorithm to be correct?

It could have been a requirement that the output
of the algorithm is _sorted_.

Let's give this notation a precise meaning.
We call the corresponding predicate [sorted']
because we will later refine the definition into
something more general that helps us a lot with
inductive proofs.
*)

(** This fails because [x2 :: s'] is not a
    structural subterm of [s] *)
Fail Fixpoint sorted' s : bool :=
  if s is x1 :: x2 :: s' then
    leT x1 x2 && (sorted' (x2 :: s'))
  else true.

Fixpoint sorted' s : bool :=
  if s is x1 :: ((x2 :: s') as tail) then
    leT x1 x2 && (sorted' tail)
  else true.

(** The obvious definition we came up with is not
    very easy to work with.
    We would see it later when trying to prove
    that [insert] function preserves sortedness. *)


(** So instead we are going to use Mathcomp's
    [sorted] predicate, which is based on the notion
    of [path]. *)
Print sorted.
(**
sorted =
fun (T : eqType) (leT : rel T) (s : seq T) =>
if s is x :: s' then path leT x s'
else true
: forall T : Type, rel T -> seq T -> bool
*)

Print path.
(**
path =
fun (T : Type) (e : rel T) =>
fix path (x : T) (p : seq T) {struct p} : bool :=
  if p is (y :: p') then e x y && path y p'
  else true
: forall T : Type, rel T -> T -> seq T -> bool
*)

(**
path e x p means
x `e` x1 `e` x2 `e` ... `e` xn,
where
p = [:: x1; x2; ... xn],
[`e`] means infix invokation of relation [e]
 *)

(** With the modified definition the helper lemma
    is much easier to prove (exercise): *)
Lemma sorted_cons x s :
  sorted leT (x :: s) -> sorted leT s.
Proof.
by case: s => //= x1 s /andP[].
Qed.




(**
It's easy to see that requiring just sortedness
of the output list is a rather weak specification --
a function always returning an empty list would
also be correct: *)

Definition fake_sort s : seq T := [::].

Lemma sorted_fake_sort s : sorted leT (fake_sort s).
Proof. by []. Qed.

(**
We could have tried to rectify this situation
by adding some unit tests

    Check erefl : sort [::] = [::].
    Check erefl : sort [:: 1] = [:: 1].
    Check erefl : sort [:: 1; 2] = [:: 1; 2].
    Check erefl : sort [:: 2; 1] = [:: 1; 2].

But this misses the point: we take some knowledge
of the invariants of [sort] convert it into a bunch
of tests and throw away the rest. Whoever gets to read
this will have to reconstruct the invariants from those
unit tests, and this is not an easy task.
 *)

(**
Hence, our next observation --
the function should NOT forget about elements of
the input list:

  forall x : T, x \in s -> x \in (sort s)

or, we can write the above statement using {in _, _} notation as

  {in s, forall x, x \in sort s}.

A little thinking reveals this is a pretty weak spec:
a function may (in principle) add extra elements
to the output, so we need to disallow that:

  forall x : T, x \in s = x \in (sort s)

Remark:
  Since our implementations are going to be
  parametric (generic), the only way the extra
  elements may occur in the output list is by
  repeating some elements of the input list,
  so the above tweak of the spec does not
  actually buy us anything.

The current version of the spec is still not strong
enough: it does not take into account possible
duplicates in the input list, e.g. the following is
true, while this is not what we meant -- let's assume
s = [:: 0; 0; 0] and that (sort s) = [:: 0; 0],
then the spec above still holds:
  forall x, x \in [:: 0; 0; 0] = x \in [:: 0; 0]

What we actually care about is to keep the elements
together with their repective number of occurences.

  forall x : T,
    count (pred1 x) s = count (pred1 x) (sort s),

where [pred1 x] means [fun y => x == y].

You may have recognized the proposition
  forall x : T,
    count (pred1 x) s = count (pred1 x) (sort s)

as expressing the notion of _permutation_ of two lists.
 *)


(**
There is one more concern w.r.t. the spec we came up
with so far -- it's non-computable as it requires us
to compute [count]-expressions over a possibly
infinite type [T], because we quantify the whole
statement over [T].
Intuitively, we know that for any two lists we can
compute if one is a permutation of the other when we
have decidable equality over the type of elements.

Mathcomp introduces a computable of notion of
equivalence up to permutation: [perm_eq] defined
as follows:
*)

Print perm_eq.
(**
perm_eq =
fun (T : eqType) (s1 s2 : seq T) =>
  all
    [pred x | (count_mem x) s1 == (count_mem x) s2]
    (s1 ++ s2)

is equivalent to

  all
    [pred x | (count_mem x) s1 == (count_mem x) s2]
    s1
  &&
  all
    [pred x | (count_mem x) s1 == (count_mem x) s2]
    s2

: forall T : eqType, seq T -> seq T -> bool

where
Notation count_mem x := (count (pred1 x))
*)


(**
Moreover, any two lists [s1] and [s2] that are
a permutation of each other, give us the following
property which is universal for _any_ predicate [p]:
  forall p : pred T,
    count p s1 = count p s2,
expressed as a [reflect]-predicate:
*)
About permP.
(**
permP :
   forall (T : eqType) (s1 s2 : seq T),
   reflect (count^~ s1 =1 count^~ s2)
           (perm_eq s1 s2)
*)


(**
Alternatively, the notion of permutation may be
expressed as a binary _inductive_ predicate:
 *)
Section InductivePermutations.
Variable A : Type. (** Notice it does not have to be [eqType] *)

Inductive pperm : seq A -> seq A -> Prop :=
| permutation_nil : pperm [::] [::]
| permutation_skip a v1 v2 of
    pperm v1 v2 : pperm (a :: v1) (a :: v2)
| permutation_swap a b v1 v2 of
    pperm v1 v2 : pperm [:: a, b & v1] [:: b, a & v2]
| permutation_trans v1 v2 v3 of
    pperm v1 v2 & pperm v2 v3 : pperm v1 v3.

Hint Constructors pperm : core.

(**
The pros of this definition:
- it can be used to work in a more general setting
  where we don't have decidable equality;
- we can do induction on the proofs of two lists
  being a permutation of each other.

The cons is, of course, it does not compute.
 *)

(** Exercise: [pperm] is reflexive *)
Lemma pperm_refl v :
  pperm v v.
Proof.
by elim: v => // x v IHv; constructor.
Qed.

(** [pperm] is symmetric *)
Lemma pperm_sym v1 v2 :
  pperm v1 v2 <-> pperm v2 v1.
Proof.
suff {v1 v2} L : forall v1 v2,
  pperm v1 v2 -> pperm v2 v1 by split; apply: L.
move=> v1 v2; elim=> [*|*|*|] //.
- by constructor.
- by constructor.
move=> ??? _ P21 _ P32.
by apply: permutation_trans P32 P21.

Restart. Show.

(** If we do induction on, let's say, [v1] the proof is significantly harder *)
suff {v1 v2} L : forall v1 v2,
    pperm v1 v2 -> pperm v2 v1 by split; apply: L.
(** Let's prove an inversion lemma locally (we would want it at top level, actually) *)
have Inv0l : forall v, pperm [::] v -> v = [::].
- case=> // x v.
  move: {-2}[::] (erefl (Nil A)) => w eq PP; move: PP eq.
  elim=> // z1 z2 z3 _ z21 _ z32 z1n.
  by rewrite -z21 // z32 // z21.
elim=> [| x v1 IHv1]; first by move=> v2 /Inv0l->.
(** You will need more inversion lemmas to finish the proof *)
Abort.

(** Optional exercise: finish the proof of [pperm_sym] by list induction.
 *)
End InductivePermutations.


(** * Upshot:
Our final notion of correctness of sorting algorithms
can be expressed semi-formally as follows
  sorted (sort s)  /\  perm_eq s (sort s)
*)




(** Let's try proving these properties for the
    insertion sort algorithm we implemented *)

(** * The output is sorted *)


(* Local Notation sorted := (sorted leT). *)

Lemma sort_sorted s :
  sorted leT (sort s).
Proof.
elim: s=> [//| x s IHs /=].
(** We need the fact that [insert] preserves
    sortedness. Let's prove it as a standalone lemma
 *)
Abort.

Lemma insert_sorted e s :
  sorted leT s ->
  sorted leT (insert e s).
Proof.
elim: s=> [//| x1 s IHs].
move=> /=.
move=> path_x1_s.
case: ifP=> [e_le_x1 | e_gt_x1].
- by rewrite /= e_le_x1 path_x1_s.
(** Notice that we lack one essential fact about
    [leT] -- totality *)
Abort.

Hypothesis leT_total : total leT.
Print total.
(**
total =
fun (T : Type) (R : rel T) =>
  forall x y : T, R x y || R y x
*)

Lemma insert_sorted e s :
  sorted leT s ->
  sorted leT (insert e s).
Proof.
elim: s=> [//| x1 s IHs].
move=> /= path_x1_s.
case: ifP=> [e_le_x1 | e_gt_x1].
- by rewrite /= e_le_x1 path_x1_s.
have:= leT_total e x1.
rewrite {}e_gt_x1.
move=> /= x1_le_e.
move: path_x1_s=> {}/path_sorted/IHs.
case: s=> [|x2 s]; first by rewrite /= x1_le_e.
move=> /=.
case: ifP.
- move=> /=.
  move=>-> /= ->.
  by rewrite x1_le_e.
  (** We are moving in circles here, let' steps back
      and generalize the problem. *)
Abort.

Lemma insert_path z e s :
  leT z e ->
  path leT z s ->
  path leT z (insert e s).
Proof.
move: z.
elim: s=> [/=| x1 s IHs] z.
- by move=>->.
move=> z_le_e.
move=> /=.
case/andP=> z_le_x1 path_x1_s.
case: ifP.
- by rewrite /= z_le_e path_x1_s => ->.
move=> /= e_gt_x1.
rewrite z_le_x1.
have:= leT_total e x1.
rewrite {}e_gt_x1 /= => x1_le_e.
exact: IHs.
Qed.
(** Optional exercise: refactor the proof above into an idiomatic one *)


Lemma insert_sorted e s :
  sorted leT s ->
  sorted leT (insert e s).
Proof.
rewrite /sorted.
case: s=> // x s.
move=> /=.
case: ifP; first by move=> /= ->->.
move=> e_gt_x.
apply: insert_path.
have:= leT_total e x.
by rewrite e_gt_x /= => ->.
Qed.


(** exercise *)
Lemma sort_sorted s :
  sorted leT (sort s).
Proof.
  by elim: s => //= x l IHv; apply: insert_sorted.
Qed.

End InsertionSort.

Arguments sort {T} _ _.
Arguments insert {T} _ _ _.




Section SortIsPermutation.

Variable T : eqType.
Variables leT : rel T.

(** a helper lemma (exercise) *)
Lemma count_insert p e s :
  count p (insert leT e s) = p e + count p s.
Proof.
  elim: s=> //= a s.
  case: ifP=> //= _->.
  by rewrite addnCA.
  (* by rewrite addnA [p a + p e]addnC -addnA. *)
Qed.

About perm_eql.
(**
Notation perm_eql s1 s2 :=
  (perm_eq s1 =1 perm_eq s2).
 *)

Print perm_eq.
(**
perm_eq =
fun (T : eqType) (s1 s2 : seq T) =>
all [pred x | count_mem x s1 == count_mem x s2]
    (s1 ++ s2)
     : forall T : eqType, seq T -> seq T -> bool
*)


Lemma perm_sort s : perm_eql (sort leT s) s.
Proof.
Search _ (perm_eq ?s1 =1 perm_eq ?s2).
apply/permPl/permP.
(** exercise *)
elim: s=> //= x s IHs p.
by rewrite count_insert IHs.
Qed.

(** This is why we state [perm_sort] lemma
    using [perm_eql] -- it can be used as
    an equation like so
 *)
Lemma mem_sort s : sort leT s =i s.
Proof. by apply: perm_mem; rewrite perm_sort. Qed.

Lemma sort_uniq s : uniq (sort leT s) = uniq s.
Proof. by apply: perm_uniq; rewrite perm_sort. Qed.

End SortIsPermutation.



Section SortProperties.

Variable T : eqType.
Variables leT : rel T.

Lemma sorted_sort s :
  sorted leT s -> sort leT s = s.
Proof.
elim: s=> // x1 s IHs S.
move: (S)=> {}/sorted_cons/IHs /= ->.
move: S=> /=.
case: s=> //= x2 s.
by case/andP=> ->.
Qed.

(** Insertion sort is stable (exercise) *)
Section Stability.

Variable leT' : rel T.
Implicit Types s : seq T.

(** Hint: you are free to assume e.g.
          [transitivity] of [leT] / [leT'] should
          you need that. E.g.
Hypothesis leT_tr : transitive leT.
 *)

(** Homework exercise: insertion sort is stable *)
Lemma sort_stable s :
  sorted leT' s ->
  sorted
    [rel x y | leT x y && (leT y x ==> leT' x y)]
    (sort leT s).
Proof.
Admitted.
End Stability.

End SortProperties.

End Insertion.


(*** Phantom types *)

(**
We have seen a notation like

    {in s, forall x, x \in sort s}

Let us take it apart and see how it works.

The challenge is to transform an unknown universally
quantified proposition into a new one, i.e.
to go from
[forall x : T, a x]
to
[forall x : T, x \in s -> a x]

This is something not possible using simple notations,
unless we are willing to repeat Coq's syntax to
a certain extent.

Notation "{ 'in' d , P }" :=
  (... stuck because [forall] is inside [P]
       and we wouldn't want to redefine [forall] syntax ...).

(** With phantom types we can sort of pattern-match on
    the form of a type, just like we did before with the
    form of a term.
    Once we have the components of e.g. a proposition, we
    can rearrange those into a new one, possibly adding
    more logical connectives.
*)

 *)

(** But first let's turn to a simpler example. *)

Definition conj_swap A B
           (_ : phantom Prop (A /\ B)) : Prop :=
  B /\ A.
Notation "'{' '/|\' p '}' " :=
  (@conj_swap _ _ (Phantom Prop p)).

(** Usage: *)
Eval hnf in { /|\ False /\ True}.
(**
     = True /\ False
     : Prop
*)

(** We can go even deeper and generalize the above to
    (almost) arbitrary binary logical connectives: *)
Definition bin_conn_swap A B
           (conn : Prop -> Prop -> Prop)
           (_ : phant (conn A B)) : Prop :=
  conn B A.

Notation "'{' '|' p '}' " :=
  (@bin_conn_swap _ _ _ (Phant p)).

Eval hnf in { | False /\ True}.
Eval hnf in { | False \/ True}.

Fail Eval hnf in { | True}.


(** A couple of exceptions *)
Eval hnf in { | False <-> True}.
(** strips away [iff] _definition_ *)

Fail Eval hnf in { | False -> True }.
(** [x -> y]  means [forall (_ : x), y] *)


(** ** How does this example work? *)

Print phantom.
(**
    Variant phantom (T : Type) (p : T) : Prop :=
      | Phantom : phantom T p
*)

(* [Phantom] constructor is used
   to lift terms at the level of types *)
Check Phantom nat 42 : phantom nat 42.


Eval hnf in { | False /\ True}.
(*
This is how unification goes here (notation unfolded):

(@bin_conn_swap _  _  _     (Phantom Prop (and False True) : phantom Prop (and   False True))).
(@bin_conn_swap ?A ?B ?conn (_                             : phantom Prop (?conn ?A    ?B  ))).
*)

(**
Note: we could have utilized a simpler version of
[phantom] used when dealing with types, not terms:

  Definition bin_conn_swap A B
            (conn : Prop -> Prop -> Prop)
            (_ : phant (conn A B)) : Prop :=
    conn B A.
  Notation "'{' '|' p '}' " :=
    (@bin_conn_swap _ _ _ (Phant p)).

 *)


(** Let us go back and see how {in d, P} notation
    can be implemented *)

Definition
  prop_in1
  (T1 : Type)
  (d : mem_pred T1)
  (P : T1 -> Prop)
  (_ : phant (forall x : T1, P x))
  (* & phant (forall x : T1, P x) *)
  : Prop :=
     forall x : T1, x \in d -> P x.

Notation "{ 'in' d , P }" :=
  (prop_in1 (mem d) (Phant P)).

Print phant.
Check Phant nat : phant nat.

Section example_usage.
Variables
  (T : eqType) (a : pred T) (s : seq T).

Eval hnf in {in s , forall x, a x}.
Fail Eval hnf in {in s , exists x, a x}.

(**
     = forall x : T, x \in mem s -> a x

Note:
[seq] is an instance of [predType] -- the generic
predicate interface, supported e.g. for for lists
and sets.
This can be analyzed using the following vernacular.
  Set Printing Coercions.
  Check mem.
  Print Canonical Projections.
We look for [list <- pred_sort ( seq_predType )] entry here.
*)

End example_usage.



Section PhantomExercises.
(** *)

(** Projection using phantoms.
    Implement [swap'] definition and [swap] notation
    so that the following works: *)

(** Strictly no pattern-matching! *)

Definition swap' A B (x : A) (y : B) (_ : phantom (A * B) (x, y)) := (y, x).
Notation swap p := (@swap' _ _ _ _ (Phantom _ p)).
(** Usage: *)
Eval hnf in swap (true || false, 41 + 1).


(** Design a unification tool so that the following
    typechecks iff X and Y can be unified *)

Notation "[unify X 'with' Y ]" := (
    let
      unification := erefl : X = Y
    in True
).

(** Usage: *)
Check [unify 1 with 0 + 1].
Check [unify 1 with 1 + 0].
Check (fun n : nat => [unify 0 + n with n]).
Fail Check (fun n : nat => [unify n + 0 with n]).  (** this should fail *)

Eval cbv in (true && true) && false.

Variable T : Type.
Variable a : T.
Check [unify a with a].
Section LHS.
(** Design a tool for extracting the left-hand side expression
    from a term proving an equation *)
(* Notation "[LHS 'of' proof_of_equation ]" := *)
(*   (). *)

Variable prf_eq : true && false = false.
(* Eval cbv zeta in [LHS of prf_eq]. *)
(** The desired result = true && false *)

End LHS.
End PhantomExercises.




(*** Overview *)
(**

Idioms:
- Vanilla [remember] tactic analogue: [move: {-2}<term> (erefl <term>) => id]
- [case: ifP] -- find an [if]-expression and case split using the condition

Phantom types are like pattern-matching on terms (on a meta-level).
*)