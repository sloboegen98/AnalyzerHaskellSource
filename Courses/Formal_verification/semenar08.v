From mathcomp Require Import ssreflect ssrfun ssrbool eqtype ssrnat seq.
Set Implicit Arguments.
Unset Strict Implicit.
Unset Printing Implicit Defensive.




Section EqType.

Lemma eq_sym (T : eqType) (x y : T) :
  (x == y) = (y == x).
Proof.
  by apply/eqP/eqP.
Qed.
(* ^ Hint: use apply/view1/view2 mechanism *)


(** Exercise:
  Implement an instance of equality type for the [seq] datatype
  and test it
 *)

Definition seq_eqMixin (T : eqType) : Equality.mixin_of (seq T) := 
  Equality.Mixin (@eqseqP _).

Definition seq_eqType1 (T : eqType) : eqType := Equality.Pack (seq_eqMixin T).
Canonical seq_eqType1.
(* Print Canonical Projections. *)

Compute [:: 1; 2] == [:: 2].
Compute [:: 1; 2] == [:: 1;2].

 Fixpoint eqs {T : eqType} (l1 l2 : seq T) : bool :=
    match l1, l2 with
      | [::], [::] => true
      | (e1 :: l1'), (e2 :: l2') => (e1 == e2) && (eqs l1' l2') 
      | _, _ => false
    end.

(** Define equality type for the following datatype *)
Inductive tri :=
| Yes | No | Maybe.

Definition eq_tri (tx ty : tri) : bool :=
  match tx, ty with
    | Yes, Yes => true
    | No, No => true
    | Maybe, Maybe => true
    | _, _ => false
  end.

Lemma eq_triP : Equality.axiom eq_tri.
Proof.
  by case; case; constructor. 
Qed.

Definition tri_eqMixixn := EqMixin eq_triP.
Definition tri_eqType : eqType := EqType tri tri_eqMixixn.
Canonical tri_eqType.

(** This should not fail! *)
Check (1, Yes) == (1, Maybe).


(** Define equality type for the [Empty_set] datatype *)
(** This should not fail! *)
Check fun v : Empty_set => (1, v) == (1, v).


Lemma predU1P (T : eqType) (x y : T) (b : bool) :
  reflect (x = y \/ b) ((x == y) || b).
Proof.
Admitted.


Variables (A B : eqType) (f : A -> B) (g : B -> A).

Lemma inj_eq : injective f -> forall x y, (f x == f y) = (x == y).
Proof.
move=> f_inj x y.
by apply/eqP/eqP => [/f_inj | ->].
Qed.

Lemma can_eq : cancel f g -> forall x y, (f x == f y) = (x == y).
Proof.
  (* Search _ cancel injective. *)
  (* move=> /can_inj; apply: inj_eq. *)
  by move=> /can_inj/inj_eq.
Qed.s



Lemma eqn_add2l p m n : (p + m == p + n) = (m == n).
Proof.
Admitted.


Lemma expn_eq0 m e : (m ^ e == 0) = (m == 0) && (e > 0).
Proof.
Admitted.


Lemma seq_last_notin (s : seq A) x :
        last x s \notin s = (s == [::]).
Proof.
apply/idP/eqP; last by move=>->.
by case: s=> // h s; rewrite last_cons mem_last.
Qed.

End EqType.


`