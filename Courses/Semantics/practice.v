Require Import Arith Arith.EqNat.
Require Import Omega.

Definition id := nat.

Lemma lt_eq_lt_id_dec_nat (id1 id2 : nat) :
{id1 < id2} + {id1 = id2} + {id2 < id1} .
Proof.
    destruct (le_lt_dec id1 id2).
    2: { right. assumption. }

    destruct (le_lt_dec id2 id1).
    2: { left. left. assumption. }

    left. right.

    apply (le_lt_eq_dec id1 id2) in l.
    apply (le_lt_eq_dec id2 id1) in l0.

    destruct (l).
    destruct(l0).

    apply (Nat.lt_asymm id1 id2) in l1.
    apply l1 in l2.
    destruct l2.
    subst.
    constructor.
	assumption.
Qed.

Lemma gt_eq_gt_id_dec (id1 id2 : id):
  {id1 > id2} + {id1 = id2} + {id2 > id1}.
Proof.

    unfold gt.
    destruct (lt_eq_lt_id_dec_nat id1 id2) as [[HH|HH]|HH].
    right.
    assumption.

    left. right.
    assumption.

    left. left.
    assumption.

Qed.

Lemma le_gt_id_dec (id1 id2 : id): {id1 <= id2} + {id1 > id2}.
Proof.
    destruct (gt_eq_gt_id_dec id1 id2) as [[HH|HH]|HH].
    { right. assumption. }
    { left. omega. }
    { left. omega. }
Qed.

Lemma id_eq_dec (id1 id2 : id): {id1 = id2} + {id1 <> id2}.
Proof.
    destruct (gt_eq_gt_id_dec id1 id2) as [[HH|HH]|HH].

    { right. omega.   }
    { left. assumption. }
    { right. omega. }
Qed.

Lemma eq_id {T} x (p q:T):
  (if id_eq_dec x x then p else q) = p.
Proof.
    destruct (id_eq_dec x x) as [HH|HH].

    { reflexivity. }
    { omega. }
Qed.

Lemma neq_id {T} x y (p q:T) (NEQ: x <> y):
  (if id_eq_dec x y then p else q) = q.
Proof.
    destruct (id_eq_dec x y) as [HH|HH].
    apply (NEQ) in HH.
    destruct HH.
    trivial.
Qed.

Lemma lt_gt_id_false (id1 id2 : id)
      (GT : id1 > id2) (GT': id2 > id1):
  False.
Proof.

    (* SearchAbout lt. *)
    apply (Nat.lt_asymm id1 id2) in GT.
    assumption.
    assumption.
Qed.

Lemma le_gt_id_false (id1 id2 : id)
      (LE : id2 <= id1) (GT : id2 > id1) :
  False.
Proof.
    destruct (le_gt_id_dec id1 id2) as [HH|HH].
    omega.
    omega.
Qed.

Lemma le_lt_eq_id_dec (id1 id2 : id) (LE : id1 <= id2):
  {id1 = id2} + {id2 > id1}.
Proof.
    destruct (gt_eq_gt_id_dec id1 id2) as [[HH|HH]|HH].
    omega.
    { left. assumption. }
    { right. assumption. }
Qed.

Lemma neq_lt_gt_id_dec (id1 id2 : id) (NEQ : id1 <> id2):
    {id1 > id2} + {id2 > id1}.
Proof.
	destruct (lt_eq_lt_id_dec_nat id1 id2) as [[HH|HH]|HH].
	{ right. assumption. }
	apply (NEQ) in HH.
	destruct HH.
	{ left. assumption. }
Qed.

Lemma eq_gt_id_false (id1 id2 : id)
      (EQ : id1 = id2) (GT : id1 > id2) :
  False.
Proof.
	omega.
Qed.

Lemma ne_symm (id1 id2 : id) (NEQ : id1 <> id2) : id2 <> id1.
Proof.
	omega.
Qed.
