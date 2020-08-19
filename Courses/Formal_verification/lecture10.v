From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div seq path.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** ** Braun trees *)

(** Three Algorithms on Braun Trees - C.
Okasaki(1997):

For any given node of a Braun tree, the
left subtree is either exactly the same
size as the right subtree, or one element
larger.

Examples of Braun Trees:
      o          o
     / \       /   \
    o         o     o
   / \       / \   / \


Non-examples of Braun Trees:
      o
     / \
        o
       / \


Braun trees always have minimum height,
and the shape of each Braun tree is
completely determined by its size.

In return for this rigor, algorithms that
manipulate Braun trees are often
exceptionally simple and elegant, and need
not maintain any explicit balance
information.
 *)

Section BinaryTree.

Variable T : Type.

Inductive btree : Type :=
| BTempty
| BTnode
    (l : btree)
    (a : T)
    (r : btree).

Implicit Type bt : btree.

(** A generic binary tree size algorithm *)
Fixpoint bin_size bt : nat :=
  if bt is (BTnode l _ r) then
    (bin_size l + bin_size r).+1
  else
    0.

End BinaryTree.

Arguments BTempty {T}.
Arguments BTnode {T} l a r.
Arguments bin_size {T}.

Section BraunTree.

Variable T : Type.
Implicit Type brt : btree T.

Fixpoint is_brtree brt : bool :=
  if brt is (BTnode l _ r) then
    [&& is_brtree l,
        is_brtree r &
        (bin_size l == bin_size r)
        ||
        (bin_size l == (bin_size r).+1)]
  else
    true.

Arguments is_brtree : simpl never.

(** As for the size, with Braun trees
    we can do better! *)

Fixpoint brt_diff brt s : nat :=
  if brt is (BTnode l _ r) then
    if s == 0 then 1
    else if odd s then brt_diff l (s %/ 2)
    else brt_diff r (s.-1 %/ 2)
  else 0.

Fixpoint brt_size brt : nat :=
  if brt is (BTnode l _ r) then
    let: sr := brt_size r in
    (2 * sr + brt_diff l sr).+1
  else 0.


(** Rewrite multi-rule *)
Lemma is_brtree_node l x r :
  is_brtree (BTnode l x r) ->
  (is_brtree l * is_brtree r) *
  (bin_size r <= bin_size l) *
  ((bin_size l == bin_size r) ||
   (bin_size l == (bin_size r).+1)).
Proof.
     (* to simplify things     *)
     (* vvvvvvvvvvvvvvvvvvvvvv *)
rewrite /is_brtree -/is_brtree; case/and3P=> ->->.
case/orP; first by case: ltngtP=> // ->; rewrite orbT.
by move/eqP->; rewrite leqnSn eq_refl orbT.
Qed.

(** Helper lemma to prove [brt_diff_correct] *)
(** Exercise *)
Lemma half_double n :
  (n.*2.+1./2 = n) * (n.*2./2 = n) *
  (0 < n -> (n.*2).-1./2 = n.-1).
Proof.
Admitted.

(** Advanced exercise *)
Lemma brt_diff_correct brt (s : nat) :
  is_brtree brt ->
  (bin_size brt == s) ||
  (bin_size brt == s.+1) ->
  brt_diff brt s = bin_size brt - s.
Proof.
Admitted.

(** The spec of [brt_size] is [bin_size] *)
Lemma brt_size_correct brt :
  is_brtree brt ->
  brt_size brt = bin_size brt.
Proof.
elim: brt => // l _ x r IHr.
move=> /is_brtree_node node /=.
rewrite IHr ?node //.
rewrite brt_diff_correct ?node //.
rewrite mulSn mul1n -addnA.
by rewrite subnKC ?node // addnC.
Qed.

End BraunTree.

Arguments is_brtree {T} brt.
Arguments is_brtree_node {T l x r}.


(** Let us go back a bit and look again at
    [brt_diff_correct]. If we try proving it
    for a long time without actually succeeding
    we might start asking ourselves if it's not
    provable at all because we made a mistake
    somewhere.

    If only we had a quicker way of checking
    if it makes sense to prove a property of
    an algorithm.
 *)

(**
Property-based randomized testing to the rescue!

Key ideas:
- Write specifications as _computable_ predicates
- Generate lots of random inputes to test your functions
- "Shrink" counterexamples

One could say that property-based randomized testing sits
in the middle between hand-written unit tests and
fully formal proofs.
 *)

(** * The QuickChick plugin

https://github.com/QuickChick/QuickChick,

it is Available on the opam package manager:
    opam install coq-quickchick

QuickChick is a port of QuickCheck written around
the year 2000 by John Hughes for Haskell.

For more detail about QuickChick see
"Foundational Property-Based Testing" by
Paraskevopoulou, Hritcu, Denes, Lampropoulos, Pierce

Also, "QuickChick: Property-Based Testing in Coq" by
Lampropoulos and Pierce provides a gentle
introduction into the topic:
https://softwarefoundations.cis.upenn.edu/qc-current/index.html
 *)
(*
From QuickChick Require Import QuickChick.
Import QcDefaultNotation. Open Scope qc_scope.
Import GenLow GenHigh.
Set Warnings "-extraction-opaque-accessed,-extraction".


(** The user writes their generators and shrinkers,
    but luckily for us for sufficiently simple datatypes
    QuickChick can do it automatically *)
Derive Arbitrary for btree.
(**
GenSizedbtree is defined
Shrinkbtree is defined
*)

Derive Show for btree.
(** ShowTree is defined *)

Variable T : Type.
QuickChick (fun (bt : btree nat) =>
              brt_size bt == bin_size bt).
(**
BTnode BTempty 0 (BTnode BTempty 0 BTempty)
*** Failed after 3 tests and 2 shrinks. (0 discards)
*)
Definition bad := BTnode BTempty 0 (BTnode BTempty 0 BTempty).
Compute bin_size bad.  (* = 2 *)
Compute brt_size bad.  (* = 3 *)

(** This does not look like a valid counterexample
    because the right subtree is bigger than the left
    one.
    Oh, wait, we forgot to constraint the inputs.
 *)

Time QuickChick (fun bt => is_brtree bt ==>
                   (brt_size bt == bin_size bt)).
(**
+++ Passed 10000 tests (0 discards)
Finished transaction in 1.474 secs (0.328u,0.052s) (successful)
*)


(** Using QuickChick can be a nice way of figuring out
    the precodintions to the lemmas of interest,
    i.e. testing helps proving!

    Moreover, since our testing code
    (and most of QuickChick itself) is written in Coq,
    we can also formally verify this code using Coq.
    That is, proving helps testing!
 *)

(** But having introduced that precondition
    we have weakened our tests, because QuickChick
    generates some amount of non-Brown trees which get
    thrown away because of a failed precondition.

    Let us check how many trees we loose:
    one can use QuickChick's [collect] facility
    to do that.
 *)

Time QuickChick (fun bt =>
  collect (is_brtree bt)
  [ ==>
     is_brtree bt =>
     brt_size bt == bin_size bt]).
(**
8008 : true
1992 : false
+++ Passed 10000 tests (0 discards)
Finished transaction in 1.535 secs (0.343u,0.05s) (successful)
*)

(** Does not look too bad, right? *)

(** Let's see what else we can get *)

Fixpoint balanced {T} (brt : btree T) : bool :=
  if brt is (BTnode l _ r) then
    [&& balanced l,
        balanced r &
        (bin_size r == bin_size l)]
  else
    true.

Time QuickChick (fun bt =>
  collect (balanced bt) true).
(**
7518 : true
2482 : false
+++ Passed 10000 tests (0 discards)
Finished transaction in 1.523 secs (0.334u,0.055s) (successful)

This means the default generator generates mostly
perfectly balanced trees.
And we have just about 500 trees out of 10,000 that are
Brown trees and not perfectly balanced.

QuickChick supports user-defined random generators
that can produce inputs with the required properties.
Even more, the user can formally verify that
the supplied random generator is sound and complete.
 *)

Section BraunTreeWrongSizeFunction.

Variable T : Type.
Implicit Type brt : btree T.

Fixpoint brt_diff' brt s : nat :=
  if brt is (BTnode l _ r) then
    if s == 0 then 1 else
    if odd s then brt_diff' l (s %/ 2)
    else brt_diff' r (s %/ 2)  (* <-   (s.-1 %/ 2) *)
  else 0.

Fixpoint brt_size' brt : nat :=
  if brt is (BTnode l _ r) then
    let: sr := brt_size' r in
    (2 * sr + brt_diff' l sr).+1
  else 0.
End BraunTreeWrongSizeFunction.

Time QuickChick (fun bt =>
  collect (is_brtree bt)
  [ ==>
     is_brtree bt =>
     brt_size' bt == bin_size bt]).
(**
239 : true
79 : false
*** Failed after 319 tests and 3 shrinks. (0 discards)
Finished transaction in 1.551 secs (0.345u,0.059s) (successful)
Counterexample:

BTnode
  (BTnode
    (BTnode BTempty 0 BTempty)
    0
    (BTnode BTempty 0 BTempty))
  0
  (BTnode
    (BTnode BTempty 0 BTempty)
    0
    BTempty)
*)


(** So writing specs and code is a subtle business.
    And property-based randomized testing can help us
    with that.
    Are there any other tools / methodologies to help?
 *)


(** * Mutation Proving *)

(**
mCoq: Mutation Proving for Analysis of Verification Projects
by K. Palmskog et al.(2019)


This is related to Mutation Testing:
- make small changes resembling faults to software system
- execute accompanying test suite on changed system
- measure how well the test suite catches introduced faults
- improve test suite and repeat


Mutation Proving:
- a mutation operator [op] is applied to a Coq project
- [op] may generate a mutant
  where specifications are different
- an [op] mutant where a proof fails during
  checking is killed
- a [op] mutant where all proofs are successfully
  checked is live

Examples of operations
- Reorder branches of if-expressions
- Replace plus with minus
- Replase a list with its tail
- ...


A practical observation:
a high amount of live mutants might indicate weak specs


But sometimes it's just hard to come up
with a precise spec, e.g. this is often the case
when talking about time/space complexity:

The key but unstated invariant of [ss] is that
its [i]th item has size [2i] if it is not empty,
so that merge sort push only performs perfectly
balanced merges... without the [[::]] placeholder
the MathComp sort becomes two element-wise insertion sort.
—Georges Gonthier

A bit of context:

Section SortSeq.

Variables (T : Type) (leT : rel T).

Fixpoint merge_sort_push s1 ss :=
  match ss with
  | [::] :: ss' | [::] as ss' => s1 :: ss'
  | s2 :: ss' => [::] :: merge_sort_push (merge s2 s1) ss'
                 ^^^^
   this can be deleted, but proofs will still go through
  end.

Fixpoint merge_sort_pop s1 ss :=
  if ss is s2 :: ss' then merge_sort_pop (merge s2 s1) ss'
  else s1.

Fixpoint merge_sort_rec ss s :=
  if s is [:: x1, x2 & s'] then
    let s1 := if leT x1 x2 then [:: x1; x2]
              else [:: x2; x1] in
    merge_sort_rec (merge_sort_push s1 ss) s'
  else merge_sort_pop s ss.

Definition sort := merge_sort_rec [::].
*)

*)

(** Braun tree as a heap *)
Section BraunTreeInsert.

Variable T : Type.
Variable leT : rel T.
Implicit Types (a e : T) (bt : btree T).

Fixpoint br_insert e bt : btree T :=
  if bt is (BTnode l a r) then
    if leT e a then
      BTnode (br_insert a r) e l
    else
      BTnode (br_insert e r) a l
  else
    BTnode
      BTempty e BTempty.

(** Optional exercise *)
Lemma br_insert_size e bt :
  bin_size (br_insert e bt) =
  (bin_size bt).+1.
Proof.
Admitted.
End BraunTreeInsert.

Arguments br_insert {T}.


(** Let us quickly test that [br_insert_size]
    does not rely on any extra assumptions and
    move on *)
(* QuickChick (fun bt =>
  bin_size (br_insert ssrnat.leq 42 bt)
  ==
  (bin_size bt).+1). *)
(**
+++ Passed 10000 tests (0 discards)
*)

Section BraunTreeInsert.

(** Exercise *)
Lemma br_insert_is_brtree T (leT : rel T) e bt :
  is_brtree bt ->
  is_brtree (br_insert leT e bt).
Proof.
  (* rewrite /is_brtree -/is_brtree. *)
  elim: bt e => //.
  move=> l IHl a r IHr e.
  case/ eqP.

Admitted.

End BraunTreeInsert.
(** Notice we haven't used the heap property yet *)



(** Another take on Braun trees *)

(** * Extrinsic vs intrinsic verification *)

From Coq Require Import Extraction Program.

Module BraunTreeIntrinsic.
Section BraunTreeIntrinsic.

Variable T : Type.

Inductive brtree : nat -> Type :=
| BrTempty : brtree 0
| BrTnode
    m (l : brtree m)
    (a : T)
    n (r : brtree n)
    of (m = n \/ m = n.+1)
  : brtree (m + n).+1.

(** What's the problem with this definition? *)
Definition brt_size' {n} (brt : brtree n) :=
  n.

End BraunTreeIntrinsic.

Arguments BrTempty {T}.

(** Let's talk about running verified
    algorithms. *)

Extraction brt_size'.

(**
val brt_size' : nat -> 'a1 brtree -> nat

let brt_size' n _ =
  n

But we do not want to keep the size
of the tree at run-time.
*)


Section BraunTree.
Variable T : Type.

(** Intrinsic verification-style spec *)
Fixpoint brt_slow_size2 {n} (brt : brtree T n)
  : {s | s = n}.
case: brt.
- by exists 0.
- move=> m' l x n' r pf.
  exists (sval (brt_slow_size2 _ l) +
          sval (brt_slow_size2 _ r)).+1.
  case: (brt_slow_size2 _ _).
  case: (brt_slow_size2 _ _).
  by move=>/= ? -> ? ->.
Defined.

Print brt_slow_size2.


Variable leT : rel T.

Fixpoint br_insert {n} (e : T)
         (brt : brtree T n)
  : brtree T n.+1.
Abort.

(** But we can now express more
    in types, e.g. we don't have use default
    values to implement a removal function *)
Fixpoint brt_remove_min {n}
         (bt : brtree T n.+1) :
  T * brtree T n.
Abort.

End BraunTree.

Extraction brt_slow_size2.
Extraction brtree.
(**
type 't brtree =
| BrTempty
| BrTnode of int * 't brtree * 't * int * 't brtree

Coq removed the proofs but
couldn't get rid of the auxilliary sizes.
*)

End BraunTreeIntrinsic.




(** ** A bit more about extraction *)

From Coq Require Import Extraction.

Print sum.
(**
Inductive sum (A B : Type) : Type :=
| inl : A -> sum A B
| inr : B -> sum A B
*)

Extraction sum.
(**
type ('a, 'b) sum =
| Inl of 'a
| Inr of 'b
*)

Print sumbool.
Extraction sumbool.
(**
Inductive sumbool (A B : Prop) : Set :=
| left : A -> sumbool A B
| right : B -> sumbool A B

type sumbool =
| Left
| Right
 *)

Print or.
Extraction or.
(**
Inductive or (A B : Prop) : Prop :=
| or_introl : A -> A \/ B
| or_intror : B -> A \/ B


(* or : logical inductive *)
(* with constructors : or_introl or_intror *)
 *)



Print sigT.
Extraction sigT.
(**
Inductive sigT (A : Type) (P : A -> Type) : Type :=
    existT : forall x : A, P x -> {x : A & P x}

type ('a, 'p) sigT =
| ExistT of 'a * 'p
*)

Print sig.
Extraction sig.
(**
Inductive sig (A : Type) (P : A -> Prop) : Type :=
    exist : forall x : A, P x -> sig P

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)
*)

Print ex.
Extraction ex.
(**
Inductive ex (A : Type) (P : A -> Prop) : Prop :=
    ex_intro : forall x : A, P x -> exists y, P y

(* ex : logical inductive *)
(* with constructors : ex_intro *)
*)


Print Equality.type.
(**
Record type : Type :=
Pack { sort : Type;  _ : Equality.mixin_of sort }
*)
Extraction eqType.
(**
type coq_type = __ mixin_of
  (* singleton inductive, whose constructor was Pack *)
*)
Extraction Equality.mixin_of.
(**
type 't mixin_of = { op : 't rel; mixin_of__1 : 't axiom }
*)


