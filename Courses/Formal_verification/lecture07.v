From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(*** Induction, continued *)


(** * Complete induction *)

(** It's also called:
    - strong induction;
    - well-founded induction;
    - course-of-values induction
 *)

(** Notice we have [P : nat -> Type], not [nat -> Prop], so
    we are going to prove a lemma more general than [lt_wf_ind] *)
Lemma ltn_ind (P : nat -> Type) :
  (forall n, (forall m, m < n -> P m) -> P n) ->
  forall n, P n.
Proof.
move=> accP M.
(** Let's generalize our goal to make it provable by regular induction *)
have := ubnP M.
(** The [have] tactic works a bit like [suffices]:
    it generates two subgoals, but in a different order, i.e.
    it asks the user to provide the proof of assertion first and
    later prove it implies the original goal.
    [have] is the main SSReflect forward reasoning tactic.
    In our case [have := term] works like [move: <term>].
*)

(** [{n : nat | M < n}] is one of the several common existential types
    in Coq. It works kind of like [exists n : nat, M < n], except that
    we can extract the first component in a computationally-relevant context. *)

move=> [] x.
elim: x M.
- by [].  (** this case is vacuously true *)
move=> n IHn M.
move/ltnSE.
(** We could try solving this by cases:
    - M < n
    - M = n
but This is not going to work because of [Prop]/[Type] disctinction. *)
Fail rewrite leq_eqVlt=> /orP[].
(** So instead we take a different approach, based on transitivity of [<]/[<=] *)
move=> le_Mn.
apply: accP.
move=> m.
(** Now we have [m < M] and [M <= n] so we can infer [m < n] *)
move/leq_trans.
move=> f.
move: (f n le_Mn).
(** But [move=> f; move: (f n le_Mn)] is so frequent there is a shorthand
    for it. *)
Undo 2.
move/(_ _ le_Mn).
(** [/(_ <term>)] applies the head of the goal stack to <[term]> *)
move/IHn.
(** And we are almost done, but let's back up a bit and show how
    to compose several views into a combined one: *)
Undo 3.
move/leq_trans/(_ le_Mn).
(** This is roughly equivalent to *)
Undo.
move=> lt_mM; move: (leq_trans lt_mM le_Mn).
(** Sometimes you really want your views to apply separately.
    Separating them like [move/V1 /V2] does not work (whitespace
    is not significant here).
    There is a special syntax for that [/V1-/V2], i.e.
    you separate them with a hyphen:
    move=> /leq_trans-/(_ _ le_Mn).
 *)
(** We can combine all three views into one *)
Undo. Show.
move/leq_trans/(_ le_Mn)/IHn.
done.

(** Let us refactor the proof into an idiomatic one *)
Restart. Show.
(** This is our script so far (I tweaked it just a bit) *)
move=> accP M.
have := ubnP M.
move=> [] x.
elim: x M => //.
move=> n IHn M.
move=> le_Mn.
apply: accP.
move=> m.
move/leq_trans/(_ le_Mn)/IHn.
done.

Restart. Show.
move=> accP M.
have [n leMn] := ubnP M.
Fail elim: n M => //. Show.
elim: n => // n IHn in M leMn *.
apply: accP.
move=> m.
move/leq_trans/(_ leMn)/IHn.
done.


(** Idiomatic solution *)
Restart. Show.
move=> accP M; have [n leMn] := ubnP M; elim: n => // n IHn in M leMn *.
by apply: accP=> m /leq_trans/(_ leMn)/IHn.
Qed.

(**
The idiom for a proof by induction over a measure [Mxy : nat] involving
variables [x], [y], ... (e.g., [size x + size y]) is
[have [m leMn] := ubnP Mxy; elim: n => // n IHn in x y ... leMn ... *.]

One more example: induction over a number of occurences of element [a] in
two sequences [s1] and [s2].
[have [n le_an] := ubnP (count a (s1 ++ s2)); elim: n => // n IHn in a le_an *.]

*)


(** * Lists and structural induction *)

From mathcomp Require Import seq path.
(** Note that we added [seq] and [path] modules to imports *)

(** [seq] is a Mathcomp's notation for [list] data type *)
Print seq.
Print list.

(**
   Inductive list (A : Type) : Type :=
   | nil : seq A
   | cons : A -> seq A -> seq A
*)

(** A simple example *)
Compute [:: 1; 2; 3] ++ [:: 4; 5].

(** List concatenation *)
Locate "++".
Print cat.

(** * Structural Induction for Lists *)

Section StructuralInduction.

Check list_ind :
forall (A : Type) (P : seq A -> Prop),
  P [::] ->
  (forall (a : A) (l : seq A), P l -> P (a :: l)) ->
  forall l : seq A, P l.

Variable T : Type.

Implicit Types xs ys zs : seq T.

Lemma catA xs ys zs :
  xs ++ (ys ++ zs) = (xs ++ ys) ++ zs.
Proof.
(** Idiomatic solution *)
by elim: xs=> //= x xs ->.
Qed.

End StructuralInduction.


(** * Classical example: list reversal function *)

(** A naive quadratic implementation *)
Fixpoint rev2 {A : Type} (xs : seq A) : seq A :=
  if xs is x::xs' then
    rev2 xs' ++ [:: x]
  else xs.

(** The standard implementation is tail recursive *)
Print rev.
Print catrev.

Lemma rev2_cat A (xs ys : seq A) :
  rev2(xs ++ ys) = rev2(ys) ++ rev2(xs).
Proof.
  elim: xs=> [| x xs IHxs /=]; first by rewrite cats0.
  by rewrite IHxs catA.
Qed.


(** Exercise *)
Lemma rev2_inv A :
  involutive (@rev2 A).
Proof.
  (* rewrite/involutive. *)
  (* rewrite/cancel. *)
  move=> s.
  elim: s=> //= a x Ixs.
  rewrite rev2_cat.
  move=> //=.
  by rewrite Ixs.
Qed.


(*** [reflect]-predicate *)


Section MotivationalExample.

Variable T : Type.

Variable p : pred T.
Print pred.
Check p : T -> bool.

Lemma all_filter (s : seq T) :
  all p s -> filter p s = s.
Proof.

(* Notation "[ 'seq' x <- s | C ]" := (filter (fun x => C) s) *)

Print filter.
Print all.

elim: s => //= x s IHs.

rewrite /is_true.
move=> /andP.
(* Set Printing Coercions. *)
rewrite /is_true.
move=> [].
move=> ->.
move/IHs.
move=>->.
done.

Search _ (_ == _) bool.

Restart.

by elim: s => //= x s IHs /andP[-> /IHs->].
Qed.

End MotivationalExample.


(** How does [andP] from above work? *)

About andP.

Print reflect.
Print Bool.reflect.

(**
    Inductive reflect (P : Prop) : bool -> Set :=
    | ReflectT : P -> reflect P true
    | ReflectF : ~ P -> reflect P false
 *)

Search _ reflect in seq.
Search _ reflect in ssrnat.

(** First, let us show that [P] if and only if [b = true]
    as two separate lemmas
  *)

Lemma introT_my (P : Prop) (b : bool) :
  reflect P b -> (P -> b).
Proof.
Set Printing Coercions.
rewrite /is_true.
Unset Printing Coercions.
case.
(** The index here works as a rewrite rule *)
- move=> _ _. done.
move=> np. move/np. case.
Qed.

(** Exercise *)
Lemma elimT_my (P : Prop) (b : bool) :
  reflect P b -> (b -> P).
Proof.
  by case.
Qed.

(** [reflect P b -> (b <-> P)] *)

(** Essentially, a [reflect] predicate connects
    a _decidable_ proposition to its decision procedure.
 *)

(** Exercise *)
Lemma reflect_lem P b :
  reflect P b -> P \/ ~ P.
Proof.
  by case=> [p | np]; [left | right].
Qed.

(** Lets look at some standard [reflect] predicates *)

Lemma andP_my (b c : bool) :
  reflect (b /\ c) (b && c).
Proof.
by case: b; case: c; constructor=> //; case.
Qed.

(** Exercise *)
Lemma orP_my (b c : bool) :
  reflect (b \/ c) (b || c).
Proof.
  case: b; case: c; constructor=> //; try by right; try by left.
  by constructor.
  by case.
Qed.

Lemma nandP_my b c : reflect (~~ b \/ ~~ c) (~~ (b && c)).
Proof. by case: b; case: c; constructor; auto; case. Qed.

(** Exercise *)
Lemma idP_my (b : bool) :
  reflect b b.
Proof.
  case: b; by constructor.
Qed.

(** * Using reflection views in intro patterns *)
Lemma special_support_for_reflect_predicates (b c : bool) :
  b /\ c -> b && c.
Proof.
move/andP.
Show Proof.
About introT.  (** [introT] view hint gets implicitly inserted *)
(**
SSReflect implicitly inserts the so-called view hints to
facilitate boolean reflection. In this case it's [introT] view hint.

Here is the syntax to do that (see ssrbool.v file):
[Hint View for move/ elimTF|3 elimNTF|3 elimTFn|3 introT|2 introTn|2 introN|2.]

The optional natural number is the number of implicit arguments
to be considered for the declared hint view lemma.

The ssrbool.v module already declares a numbers of view hints,
so adding new ones should be justified. For instance, one might need to do it
if one defines a new logical connective.
 *)

Restart.
move=> b_conj_c.

Check introT : forall (P : Prop) (b : bool), reflect P b -> P -> b.

Check @introT (b /\ c) (b && c) (@andP b c) b_conj_c.

exact: @introT (b /\ c) (b && c) (@andP b c) b_conj_c.
Qed.

(** Reflection views usually work in both directions *)
Lemma special_support_for_reflect_predicates' b c :
  b && c -> b /\ c.
Proof.
move/andP.
Show Proof.

About elimTF.

(** [elimTF] is in some sense a bit more general compared to [introT] *)

(**
elimTF : forall (P : Prop) (b c : bool),
           reflect P b -> b = c -> if c then P else ~ P
*)

Restart.

move=> Hb.
Check @elimTF (b /\ c) (b && c) true (@andP b c) Hb.
move: Hb.
move/(@elimTF (b /\ c) (b && c) true (@andP b c)).

exact: id.
Qed.

(** Why is [elimTF] so complex? Because it's applicable not only
    in the case the goal's top assumtion is of the form
    [b && c], but also [b && c = false]*)
Lemma special_support_for_reflect_predicates'' b c :
  (b && c) = false -> ~ (b /\ c).
Proof.
move/andP.
Show Proof.

Restart.
move=> Hb.
Check @elimTF (b /\ c) (b && c) false (@andP b c) Hb.

exact: @elimTF (b /\ c) (b && c) false (@andP b c) Hb.
Qed.


(** * Switching views at the goal *)

Lemma special_support_for_reflect_predicates''' (b c : bool) :
  b /\ c -> b && c.
Proof.
move=> ab.
apply/andP.  (** [apply/] syntax *)
Show Proof.  (** [introTF] view hint gets inserted *)
About introTF.
done.
Qed.

Lemma special_support_for_reflect_predicates'''' (b c : bool) :
  ~ (b /\ c) -> b && c = false.
Proof.
move=> ab.
apply/andP.  (** [apply/] syntax *)
Show Proof.  (** [introTF] view hint gets inserted *)
About introTF.
done.
Qed.


(** Specification for [eqn] -- decision procedure for equality on [nat]s *)
Lemma eqnP_my (n m : nat) : reflect (n = m) (eqn n m).
Proof.
(** One way to prove this is to turn [reflect] into a bi-implication
    and prove the two directions by induction separately.
    An idiomatic way to do that is like so *)
apply: (iffP idP).   (** [idP] -- the trivial reflection view *)

Check iffP : forall (P Q : Prop) (b : bool),
               reflect P b -> (P -> Q) -> (Q -> P) -> reflect Q b.

- by elim: n m => [|n IHn] [|m] //= /IHn->.
move=> ->. by elim: m.
Qed.


Lemma silly_example_iffP_andP (b c : bool) :
  reflect (b /\ c) (b && c).
Proof.
apply: (iffP idP).
Undo.
Check (iffP andP).
apply: (iffP andP).
- done.
done.
Qed.


(** A better example of using [iffP] with a non-[idP] argument *)
Lemma nseqP (T : eqType) n (x y : T) :
  reflect (y = x /\ n > 0) (y \in nseq n x).
Proof.
rewrite mem_nseq andbC.
apply: (iffP andP).
(* reflect (x = y) (x == y) *)
case.
(** [eqP] converts between propositional and boolean equalities *)
move/eqP.
move=>->. done.
case=>->->. rewrite eq_refl. done.

(** A more idiomatic solution *)
Restart. Show.

by rewrite mem_nseq andbC; apply: (iffP andP) => [[/eqP]|[/eqP]].
(** There is some code duplication here which can be reduced using
    [-[...]] syntax: *)
Restart.
by rewrite mem_nseq andbC; apply: (iffP andP)=> -[/eqP].
(** We cannot say just [[/eqP]] because that
    Coq expects us to provide tactics for both subgoals and not just one.
    [-] forces the case splitting interpretation
 *)
Qed.



(** * Rewriting with [reflect] predicates *)


About maxn_idPl.

Lemma leq_max m n1 n2 :
  (m <= maxn n1 n2) = (m <= n1) || (m <= n2).
Proof.
case/orP: (leq_total n2 n1) => [le_n21 | le_n12].
- Search _ (maxn ?n1 ?n2 = ?n1).
  rewrite (maxn_idPl le_n21).   (** A cool trick! *)
(** Why does this work? *)
Check (maxn_idPl le_n21).  (** OK, this is an ordinary equation,
                               no wonder [rewrite] works. *)
(** [maxn_idPl] is _not_ a function but behaves like one here.
    Let us check coercions! *)
Set Printing Coercions.
Check (maxn_idPl le_n21).   (** [elimT] get implicitly inserted *)
Unset Printing Coercions.

About elimT.

(** [elimT] is a coercion from [reflect] to [Funclass],
    This means it gets inserted when one uses a reflect view as a function.
  *)

(** Essentially we invoke the following tactic: *)

Undo. Show.
rewrite (elimT maxn_idPl le_n21).

(** Exercise: finish the proof *)
Restart. Show.

(** But let's us simplify the proof by removing the symmetrical
    case first *)
without loss le_n21: n1 n2 / n2 <= n1.
  by case/orP: (leq_total n2 n1) => le_n12; last rewrite maxnC orbC; apply.
rewrite (maxn_idPl le_n21).

Admitted.


(** * An example of a specification for a [seq] function *)

(** [all] specification *)
About allP.
(**
    forall (T : eqType) (a : pred T) (s : seq T),
    reflect {in s, forall x : T, a x} (all a s)
*)

(** Check out some other specs in the [seq] module! *)
Search _ reflect in seq.




(*** Specs as rewrite rules *)

Example for_ltngtP m n :
  (m <= n) && (n <= m) ->
  (m == n) || (m > n) || (m + n == 0).
Proof.
by case: ltngtP.

Restart. Show.

case: ltngtP.
done.
done.
move=>/=.
Abort.


Module Trichotomy.

Variant compare_nat m n :
   bool -> bool -> bool -> bool -> bool -> bool -> Set :=
  | CompareNatLt of m < n : compare_nat m n false false false true false true
  | CompareNatGt of m > n : compare_nat m n false false true false true false
  | CompareNatEq of m = n : compare_nat m n true true true true false false.

Lemma ltngtP m n : compare_nat m n (n == m) (m == n) (n <= m)
                                   (m <= n) (n < m) (m < n).
Proof.
rewrite !ltn_neqAle [_ == n]eq_sym; case: ltnP => [nm|].
  by rewrite ltnW // gtn_eqF //; constructor.
rewrite leq_eqVlt; case: ltnP; rewrite ?(orbT, orbF) => //= lt_mn eq_nm.
  by rewrite ltn_eqF //; constructor.
by rewrite eq_nm; constructor; apply/esym/eqP.
Qed.

(** Exercise (use [case: ltngtP] to solve it) *)
Lemma maxnC : commutative maxn.
Proof.
Admitted.

End Trichotomy.






(*** Coercions summary *)


(** * [is_true] coercion *)

(** We have already been using [is_true] coercion regularly.
    It's defined in ssrbool.v as follows:

    Coercion is_true : bool >-> Sortclass.
 *)

(** E.g. [is_true] makes the following typecheck *)
Check (erefl true) : true.



(** * [elimT] coercion *)

(**  Allows direct application of a reflection lemma
     to a boolean assertion.

    Coercion elimT : reflect >-> Funclass.
 *)

Section ElimT_Example.

Variables b c : bool.
Hypothesis H : b || c.

Check orP H.
Set Printing Coercions.
Check orP H.
Unset Printing Coercions.

End ElimT_Example.



(** * [nat_of_bool] coercion *)

About nat_of_bool.

About leq_b1.
About mulnb.

About count_nseq.

(** You can learn more using the following search query: *)
Search _ nat_of_bool.







(*** Overview *)
(**

Intro patterns / switches / etc.
- [-]: can be used to connect unrelated views ([move=> /V1 - /V2]) or
  to force the interpretation of [[]] as case splitting when
  multiple subgoals are generated

Tacticals:
- [in] tactical: e.g. [tactic in H1 H2 *] behaves similarly to
  [move: H1 H2; tactic=> H1 H2], but preserves the body of a definition
  and if [*] is omitted it will hide the statement of the goal
  from [tactic].
  For instance, [elim: <id> ... in <id1> ... <idn> <H1> ... <Hn> *]
  can be used to generalize the induction hypothesis.

Tactics:
- Forward reasoning: [have] tactic
- [without loss] or [wlog]: "without loss of generality"
- View mechanism: [apply/view_lemma]
- Pattern matching with equations: [case <identifier>: <term>]
- [case] tactic works on tuples of equations
- [case] tactic works on equations between constructors:
  [m.+1 = n.+1] gets converted to [m = n], or
  [(a1, b1) = (a2, b2) -> ...] into [a1 = a2 -> b1 = b2 -> ...]
- [constructor] tactic
- [rewrite] tactic supports patterns: [rewrite [<pattern>]<equation>]


Idioms:
- The idiom for a proof by induction over a measure [Mxy : nat] involving
  variables x, y, ... (e.g., [size x + size y]) is
  [have [m leMn] := ubnP Mxy; elim: n => // n IHn in x y ... leMn ... *.]
- [move/leq_trans->]

Coercions:
- [is_true]
- [elimT]
- [nat_of_bool]

*)