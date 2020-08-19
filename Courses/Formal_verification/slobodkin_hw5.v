From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat div.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.


(** PROVE THE FOLLOWING LEMMAS USING ONLY THE SSREFLECT TACTICS WE INTRODUCED EARLIER *)

(** DO NOT USE ANY LEMMAS DEFINED OUTSIDE OF THIS FILE *)

(** DO NOT USE TACTICS LIKE [tauto], [intuition], [firstorder] or any other sort of
    automation, expect automation provided by the [by], [done], [exact] tactic(al)s. *)

(** STRUCTURE YOUR PROOFS BY SUBGOALS USING [-] SYNTAX AS SHOWN DURING THE LAST LECTURE *)


Section IntLogic.

Variables A B C : Prop.

(** Exercise 1: prove that conjunction is associative  *)
Lemma andA :
  (A /\ B) /\ C -> A /\ (B /\ C).
Proof.
  case.
  (* Show Proof. *)
  case.
  move=> a b c.
  split; by [].
Qed.


(** Exercise 2: Prove that conjunction distributes over disjunction: *)
Lemma conj_disjD :
  A /\ (B \/ C) -> (A /\ B) \/ (A /\ C).
Proof.
  case.
  move=> a.
  case.
    - move=> b.
      by left.
    - move=> c.
      by right.
Qed.


(** Exercise 3: Prove that disjunction distributes over conjunction: *)
Lemma disj_conjD :
  A \/ (B /\ C) -> (A \/ B) /\ (A \/ C).
Proof.
case.
  - move=> a.
    split; by left.
  - case.
    move=> b c.
    split; by right.
Qed.


(** Exercise 4 *)
Lemma notTrue_iff_False :
  (~ True) <-> False.
Proof.
  split.
  - case. exact: I.
  - case.
Qed.
(** Hint 1: use [case] tactic on a proof of [False] to apply the explosion principle. *)
(** Hint 2: to solve the goal of the form [True], use [exact: I], or simple automation. *)


(** Exercise 5: prove that implication is transitive. *)
Lemma imp_trans :
  (A -> B) -> (B -> C) -> (A -> C).
Proof.
  move=> ab bc.
  exact: (fun a => bc (ab a)).
Qed.


(** Exercise 6: double negation elimination works for [False] *)
Lemma dne_False :
  ~ ~ False -> False.
Proof.
  by case.
Qed.


(** Exercise 7: double negation elimination works for [True] too. *)
Lemma dne_True :
  ~ ~ True -> True.
Proof.
  move=> ntrue.
  exact: I.
Qed.


(** Exercise 8: LEM is compatible with intuitionistic logic *)
Lemma LEMisNotFalse :
  ~ ~ (A \/ ~ A).
Proof.
  move=> nana.
  apply: (nana).
  right.
  move=> a.
  apply: nana.
  left.
  exact: a.
Qed.
(** Hint : use [apply: (identifier).] to apply a hypothesis from the context to the goal
           and keep the hypothesis in the context (SSReflect removes hypotheses from the context by default). *)


(** Exercise 9: weak form of Peirce's law *)
Lemma weak_Peirce :
  ((((A -> B) -> A) -> A) -> B) -> B.
Proof.
  move=> abaab.
  apply: (abaab).
  move=> aba.
  apply: aba.
  move=> a.
  apply: abaab.
  move=> aba2.
  apply: a.
Qed.

End IntLogic.


Section EquationalReasoning.

Variables A B : Type.

(** Exercise 10: Reflexivity *)
Lemma eqext_refl (f : A -> B) :
  f =1 f.
Proof.
  move=> a.
  by [].
Qed.


(** Exercise 11: Symmetry *)
Lemma eqext_sym (f g : A -> B) :
  f =1 g -> g =1 f.
Proof.
  move=> fg a.
  rewrite fg.
  by [].
Qed.
(** Hint: [rewrite] tactic also works with universally quantified equalities.
          I.e. if you have a hypothesis [eq] of type [forall x, f x = g x],
          you can use [rewrite eq] and Coq will usually figure out the concrete [x]
          it needs to specialize [eq] with, meaning that [rewrite eq] is essentially
          [rewrite (eq t)] here. *)


(** Exercise 12: Transitivity *)
Lemma eqext_trans (f g h : A -> B) :
  f =1 g -> g =1 h -> f =1 h.
Proof.
  move=> fg gh a.
  rewrite fg.
  rewrite gh.
  by [].
Qed.

End EquationalReasoning.



(** Optional exercise *)
Lemma nlem (A : Prop):
  ~ (A \/ ~ A) -> A.
Proof.
Qed.

(** Optional exercise *)
Lemma DNE_iff_nppp :
  (forall P, ~ ~ P -> P) <-> (forall P, (~ P -> P) -> P).
Proof.

Qed.


