From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq path.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


Section InsertionSort.

Variable T : eqType.
Variable leT : rel T.
Implicit Types x y z : T.

(** Insert an element [e] into a sorted list [s] *)
Fixpoint insert e s : seq T :=
  if s is x :: s' then
    if leT e x then e :: s
    else x :: (insert e s')
  else [:: e].

(** Sort input list [s] *)
Fixpoint sort s : seq T :=
  if s is x :: s' then insert x (sort s')
  else [::].

Hypothesis leT_total : total leT.

(** Optional exercise: refactor the following proof into an idiomatic one *)
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


(** Optional exercise: refactor the following proof into an idiomatic one *)
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


Lemma sort_sorted s :
  sorted leT (sort s).
Proof. by elim: s => //= x s IHs; apply: insert_sorted. Qed.

End InsertionSort.



Section InsertionSortFilter.

Variable T : eqType.
Variables leT leT' : rel T.
Implicit Types s : seq T.

Hypothesis leT_total : total leT.
Hypothesis leT_tr : transitive leT.

Lemma filter_insertF (p : pred T) x s :
  ~~ p x ->
  filter p (insert leT x s) = filter p s.
Proof.
  move=> px.
  move: (px).
  elim: s=> //=.
  - by case: ifP.
  move=> a l IH.
  case: ifP=> /=.
  - by case: ifP.
  by rewrite IH.
Qed.

Lemma filter_insertT (p : pred T) x s :
  p x ->
  sorted leT s ->
  filter p (insert leT x s) = insert leT x (filter p s).
Proof.
  move=> px sorted_s.
  move: (sorted_s).
  move: (px).

  elim s=> //=.
  - by case: ifP.
  move=> a l IH.
  case: ifP=> //=.
  - case: ifP=> //=.
    case: ifP=> //=.
    + by case: ifP.
    move=> npa _ x_lt_a _ path_a_l.

    (* Unset Printing Notations. *)
    rewrite -IH=> //=.


admit.
Admitted.

Lemma filter_sort p s :
  filter p (sort leT s) = sort leT (filter p s).
Proof.
  elim: s => //= x l IHv.
  case: ifP=> //=; rewrite -IHv.
  - move=> px.
    eapply filter_insertT; eauto.
    by apply: sort_sorted.
  - move=> npx.
    eapply filter_insertF; eauto.
    by rewrite npx.
Qed.



















(**
SPOILER ALERT
Read the following only if you get stuck doing this exercise


Hints:

(1) Introduce helper lemma

Lemma filter_insertF (p : pred T) x s :
  ~~ p x ->
  filter p (insert leT x s) = filter p s.

and another one for the case when [p x] holds.




(2) If the second lemma mentioned in hint (1) is not provable,
    make sure you have all the necessary assumptions.



(3) If hints (1) and (2) didn't really help, here is the answer

Lemma filter_insertT (p : pred T) x s :
  p x ->
  sorted leT s ->
  filter p (insert leT x s) = insert leT x (filter p s).




(4) To prove the helper lemmas reuse lemmas from the [InsertionSort] section.


 *)

End InsertionSortFilter.





(** Optional (advanced) exercise *)
Section InsertionSortStable.

Variable T : eqType.
Variables leT leT' : rel T.
Implicit Types s : seq T.

(** Hint: you are free to assume e.g.
          [transitivity] of [leT] / [leT'] should
          you need that. E.g.
Hypothesis leT_tr : transitive leT.
 *)

Hypothesis leT_total : total leT.


(** Homework exercise: insertion sort is stable *)
Lemma sort_stable s :
  sorted leT' s ->
  sorted
    [rel x y | leT x y && (leT y x ==> leT' x y)]
    (sort leT s).
Proof.
Admitted.
End InsertionSortStable.




(** Use phantom types to solve the following exercises *)
Section PhantomTypes.

(** Properties of arbitrary binary relations (not necessarily decidable) *)


(** A functional (a.k.a. deterministic) relation: *)
Definition functional {X : Type} (R : X -> X -> Prop) : Prop :=
  forall (s s1 s2 : X), R s s1 -> R s s2 -> s1 = s2.

Lemma func1 :
  functional (fun x y => x.*2 == y).
Proof.
  move=> x y1 y2.
  move/eqP.
  move=> xy1.
  move/eqP.
  by rewrite -xy1.
Qed.

Lemma func2 :
  ~ functional (fun x y => (x.*2 == y) || ((x, y) == (0,1))).
Proof.
  rewrite/ functional.
  move=> foo.
  move: (foo 0 1 0).
  rewrite double0 xpair_eqE.
  move=> /=.
  rewrite (eq_refl 1).
  move=> foo2.
  by move: (foo2 is_true_true is_true_true).
Qed.



(** Define a notation such that {In C, functional R} restricts the domain of the relation [R] like so:

  forall (s s1 s2 : X), C s -> R s s1 -> R s s2 -> s1 = s2

And prove the following lemma:
*)


(* Definition
  prop_in1
  (T1 : Type)
  (d : mem_pred T1)
  (P : T1 -> Prop)
  (_ : phant (forall x : T1, P x))
  (* & phant (forall x : T1, P x) *)
  : Prop :=
     forall x : T1, x \in d -> P x.

Notation "{ 'in' d , P }" :=
  (prop_in1 (mem d) (Phant P)). *)


  (* Definition swap' A B (x : A) (y : B) (_ : phantom (A * B) (x, y)) := (y, x).
  Notation swap p := (@swap' _ _ _ _ (Phantom _ p)). *)

Definition inC
            (X : Type)
            (C : X -> Prop)
            (R : X -> X -> Prop)
            (F : Prop -> Prop)
            (* (_ : Phantom ) *)
            : Prop 
                := forall x y, C x -> F (R x y).

Notation "{ 'In' C , P }" :=
  (@inC _ C _ _ P) (at level 0).

Lemma func3 :
  {In (fun n => 0 < n), functional (fun x y => (x.*2 == y) || ((x, y) == (0,1)))}.
Proof.
  move=> //=.
  move=> x pos_x.
  rewrite/functional.
  move=> s s1 s2.
  case/ orP.

Admitted.

End PhantomTypes.